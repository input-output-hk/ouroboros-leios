# Memo: emulating wired backbone loss for diffusion sim

## Working example

A long-haul TCP flow on a hypothetical Sydney↔Tokyo path that uses only fiber and routers — no Wi-Fi, no cellular, no satellite — i.e., submarine cables and core routers throughout.
Carrier-backbone RTT for that city pair is approximately 175 ms (Epsilon's published city-pair table); end-to-end RTT including last-mile and host overhead can run higher (200–250 ms), but the carrier figure is the working number used below.

The analysis deliberately makes no assumption about link bandwidth.
The key result we are after is that single-flow CUBIC's steady-state throughput is determined by RTT and loss rate, *not* by the bottleneck link's nominal capacity (as long as the link is fast enough that the equilibrium cwnd, not the link rate, is binding).
That is precisely why the long-fat-network problem persists across modern provisioning: scaling up the link does not scale up the flow.

## Sources of loss on a wired backbone path

These are the loss sources that contribute on a healthy Tier-1 path, in rough order of contribution.

1. **AQM background drops at congested router interfaces.**
   Modern backbone routers run RED/CoDel/PIE on bottleneck queues, dropping near-uniformly when buffer occupancy crosses thresholds.
   Drops are uncorrelated, single-packet, and steady-state aggregate is roughly 0.001–0.01 % on a well-provisioned long-haul path.
   This is both the most consistent loss source and the most relevant one for our sim purposes.

2. **Microbursts at oversubscribed peering interfaces.**
   When a transient burst overruns a buffer, packets are tail-dropped in correlated runs of 5–50 packets.
   Frequency on a healthy backbone path is minutes to hours apart.

3. **BGP convergence / repathing.**
   A fiber cut or maintenance event withdraws a route; convergence takes hundreds of milliseconds during which packets blackhole.
   On a stable transpacific path these events are days to weeks apart.

4. **Optical PHY errors.**
   Coherent submarine cables run pre-FEC BER ~10⁻³ and post-FEC ~10⁻¹², so at the IP layer this contribution is effectively zero.

5. **Router CPU / forwarding glitches.**
   Negligible on healthy gear.

For our sim, modeling (1) alone — uniform loss at p ≈ 10⁻⁴ to 10⁻⁵ — captures the dominant phenomenon.
Adding (2) is reasonable for stress testing but should be configured with rare large bursts, not frequent small ones.

## Why even tiny AQM-style loss caps single-flow throughput

### Mathis bound (Reno)

For Reno-style AIMD under uniform loss rate p, steady-state throughput is:

```
T ≈ MSS · sqrt(3/2) / (RTT · sqrt(p))
```

With MSS = 1448 and RTT = 0.175 s:

| p          | Reno throughput |
| ---------- | --------------- |
| 10⁻⁴       | ~8 Mbit/s       |
| 10⁻⁵       | ~26 Mbit/s      |

Note this is independent of any specific link bandwidth — the Mathis derivation never invokes a link rate, only the per-flow loss-and-recovery cycle.

### CUBIC equilibrium

CUBIC's growth law is more aggressive than Reno's and yields a higher equilibrium throughput on a long-RTT path.
The clean derivation is self-consistent: in steady state, CUBIC's recovery period K must equal the mean inter-loss interval *at whatever throughput X the flow is actually carrying* — not at the link's saturation pps, which is what the flow cannot reach in the first place.

CUBIC reaches W_max along its cubic curve in time:

```
K = (W_max · (1−β) / C)^(1/3)        with β = 0.7, C = 0.4
```

By Little's law, time-averaged cwnd ≈ X · RTT, so W_max ≈ X · RTT (modulo a profile-shape factor from time-averaging the cubic curve).
At throughput X under uniform loss p, mean inter-loss interval is 1/(X · p).
Setting K = 1/(X · p) and solving for X gives a closed form:

```
X ≈ 1.05 · RTT^(−1/4) · p^(−3/4)   packets/s
```

With RTT = 0.175 s and MSS = 1448:

| p          | CUBIC equilibrium W_max | CUBIC throughput |
| ---------- | ----------------------- | ---------------- |
| 10⁻⁴       | ~310 segs (~450 KB)     | ~19 Mbit/s       |
| 10⁻⁵       | ~1740 segs (~2.5 MB)    | ~106 Mbit/s      |

Like the Mathis bound, this depends only on RTT, p, and CUBIC's parameters — not on the link rate.
The bottleneck link enters only as an upper bound: if the link can carry less than the equilibrium throughput, X is capped by the link instead.

Reality is somewhat worse than these absolute numbers.
Linux's fast-convergence heuristic ratchets W_max downward whenever a loss arrives before cwnd has reached the previous W_max, and under Poisson loss a meaningful fraction of cycles hit early.
The deterministic-K analysis above ignores that, so the table is an upper bound; observed throughput sits somewhere below it.

### Net result

On a 175 ms RTT transpacific path with realistic AQM-style background loss, single-flow throughput is bounded in absolute terms regardless of how fast the underlying link is:

- At p ≈ 10⁻⁴ (somewhat lossy, e.g. a congested peering interface): Reno ~8 Mbit/s, CUBIC ~19 Mbit/s.
- At p ≈ 10⁻⁵ (well-provisioned backbone): Reno ~26 Mbit/s, CUBIC ~106 Mbit/s.

Once a path of this RTT has any AQM background loss, scaling the bottleneck link past these per-flow ceilings does nothing for a single flow; the cwnd dynamics are the binding constraint.
This is the long-fat-network problem TCP has had since the 1990s, documented as a primary motivation for CUBIC itself (RFC 8312) and the broader literature on TCP performance over high-BDP paths.

We have not directly measured throughput on a real Sydney↔Tokyo TCP flow, so the supposition that production paths of that shape exhibit similar single-flow behavior is plausible from the analysis above but not empirically confirmed in this memo.
If a stronger claim is needed, an M-Lab/NDT or RIPE Atlas measurement campaign on a representative path could ground it.

## Implication for the diffusion logic

The two production workarounds are parallel flows and BBR.

Parallel flows divide work across N concurrent connections, each running independent congestion control on the shared bottleneck.
The aggregate can avoid the per-connection Mathis ceiling, but introduces a coordination problem: each flow runs its own loop with no awareness of the others.
The team views this as harder to reason about than running one congestion control algorithm per connection.

BBR sidesteps the problem by ignoring loss as the congestion signal.
It models the bottleneck via measured delivery_rate and min_rtt and converges to near the actual bottleneck capacity regardless of AQM background loss rate, so the per-flow ceiling above does not bind.
It keeps the model simple — one congestion control algorithm per connection, no coordination required.

For these reasons, BBR is the recommended congestion control for good utilization on long-RTT links with realistic backbone loss.

## Aside: tuning CUBIC's parameters is not a third option

Linux exposes CUBIC's K-formula parameters — C (via `bic_scale`, default ≈ 0.4) and β (via `beta`, default ≈ 0.7) — as writable in `/sys/module/tcp_cubic/parameters/`.
Raising `bic_scale` ~8×, raising `beta` toward 0.85, and disabling `fast_convergence` would roughly double single-flow throughput on our 175 ms / p=10⁻⁴ example — from ~19 Mbit/s to ~38 Mbit/s — by shrinking K from ~7 s to ~3.5 s, so CUBIC could actually finish recovery cycles before the next loss arrives.

We are not pursuing this, for three reasons.

First, the parameters are module-global, not per-connection.
Every CUBIC flow on the host uses the new values, so the result would be a non-standard CUBIC that does not correspond to anything deployed in the wild.

Second, the resulting CUBIC would be RFC-non-compliant.
It would be unfair to other concurrent flows on shared bottlenecks and not safe to ship.

Third, and most importantly, this does not address the underlying mismatch: loss-as-signal is the wrong feedback for noisy-but-uncongested links.
Aggressive-CUBIC makes CUBIC less anemic; it does not make CUBIC the right tool.
BBR remains the cleaner answer.

Tuning the sim toward something we cannot deploy teaches us nothing actionable.
