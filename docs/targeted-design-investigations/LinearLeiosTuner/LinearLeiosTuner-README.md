LeiosTuner.html is a interactive Dynamic HTML calculator, derived from the template at the bottom of this Markdown file.

Curly braces {} within this Markdown file are to be interpreted as macros.
The corresponding Dynamic HTML file will replace these macros with dynamic elements that animate their semantics.

- The syntax {input VAR} is replaced with an HTML input element and binds a global variable VAR to its current value.
  The input element should be labeled by the variable name "VAR =" and have a high-visibility border.
  The input element should stick to the top of the viewing area when the user scrolls past them, no matter how far past.

- The syntax {eval ...} is replaced with a script element that will render as the value of the given expression and will update itself whenever any of the global variables in it change their value.

- The syntax {let VAR be ...} is similar to {eval ...}, but in addition rendering as the current value it also updates the value of the given global variable.

- The syntax {insert plot N} renders the Nth plot.
  There are three plots total, defined in the next sections.

- The syntax {hr} is a classy looking section break.

## Plot 1

The first plot is titled "Arrival rate of inter-RB gaps ≥ L on a g-chain".
It's a step plot portraying the probability mass holding times in a renewal process defined by L (truncating x-axis after 95% cumulative).
Repeatedly toss a coin that's biased 19:1 towards heads.
The renewal process jumps when a run of L or more heads ends.
The plot begins at x=0 and stops at the least value of x whose cumulative probability exceeds 95%.

For example, suppose L=3; then

```
0         1         2         3
0123456789012345678901234567890123456789
HTHTHTHHHTTHHHTTTHTHHTTHTHHHHHHTHHHHT...
      ---  ---           ------ ----
```

has four jumps, at 9, 14, 31, and 36.
There're thus three holding times: 14-9=5, 31-14=17, 36-31=5.

(The PMF can be computed efficiently via the linear recurrence

```
f(g) = f(g-1) − α · f(g-L-1)        with α := q · p^L
f(g) = 0  for g ≤ L,    f(L+1) = α
```

— derivable from the renewal-cycle PGF φ_G(z) = α · z^(L+1) / (1 − z + α · z^(L+1)), itself a one-line consequence of decomposing the post-jump toss stream into i.i.d. cycles (each = one geometric H-run length R ≥ 0 followed by a T; a cycle "fires" iff R ≥ L, with probability p^L). The recurrence runs in O(1) per step, fast enough for values up to L=200, and its plot can be downsampled by uniform stride to merely several thousand points---together these prevent the user from noticing laggy response.)

The plot includes rug stems that highlight 19 quantiles 5%, 10%, 15%... 85%, 90%, and 95%.
(Recall that the x-axis is already truncated at the 95% quantile.)
The stems for 25%, 50%, and 75% are taller than the others, and 50% taller still.

## Plot 2

The second plot is titled "Theoretical average capacity (with 100% stake participating, max EBs, succeed if L gap)".
It's another step plot, showing MaxSize divided by the mean holding time for all run lengths from 0 to ⌈L×4÷3⌉, with the value for L highlighted.
It has a second y-axis, which is the same shape as the first y-axis, but each y2 label is the same-height y1 label÷MaxSize×100% per second.
There is also a constant line plotted in orange at y2 = f = 5% per second (f, not g!); its describe as the protocol's worst-case protocol network usage in order to achieve the corresponding capacity.

## Plot 3

The third plot is titled "How quickly do Mempools need to refill, given L and g?".
It's another step plot, showing six curves, each the probability that at most M jumps occur within the k tosses immediately following some arbitrary jump, for M=0 to M=5.
The x-axis ranges from k=0 to k=30×L.

For each curve, the probabilities are calculated via a 2D Markov calculation.

## Template

title: Linear Leios Tuner

This page visualizes the consequences of different values of {input L, default 14, both a number input and a coupled slider} between 2 and 200.
L is the sum 3×L_hdr + L_vote + L_diff from the Linear Leios specification.

One calculation we've often considered is the probability of the leader schedule itself preventing an EB from succeeding: Linear Leios allows an EB to be certified only by the subsequent RB and only if that RB arises at least L slots later.
Before we introduce the math, a corresponding clarification is due.

While we do often refer to the "leader schedule" as the limiting factor, that habit tacitly assumes the adversary is not attacking Praos.
In other words, it assumes that the density of the RBs on the best Praos chain are determined by the leader schedule.
The relevant parameter is f = 5%, the Praos _active slot coefficient_.

When not under attack, f causes the Praos chain to grow by one block every 1/f=20 seconds, on average.
When under attack, however, the honest parties will be unable to communicate as effectively, and so some of their elections in the leader schedule will be wasted on short forks instead of them all contributing as growth of the best single chain.
We introduce a variable {input g, default 5%, both a number input and a coupled slider} between 1% and f=5% to model this.
When g = f = 5%, the adversary is not interfering with Praos.
When g < f, they are, and the difference determines the degree of their success---this numeric quantity is ad-hoc, but useful enough for our other calculations in this memo.

P(too dense | L={eval L} g={eval g}) = 1 - (1 - g)<sup>L</sup> = 1 - {eval (1 - g)^L} = {eval 1 - (1 - g)^L}.

A g-chain will, on average, need to announce N = (1 - g)<sup>-L</sup> = {eval let N be (1 - g)^(-L)} EBs for g to allow one of them to succeed.
That's the N for which N × (1 - P(too dense | L={eval L} g={eval g})) = 1.

A g-chain will, on average, announce one EB per 1/g={eval 1/g} seconds.
Therefore, on average, there will be N ÷ g = {eval N ÷ g} seconds between EBs not prevented by g.

Beyond just the average N ÷ g, we can also calculate the whole probability mass function of that duration.
The model is tosses of a (1-g):g biased coin, where every run of at least L heads terminated by a tails is an EB that the g didn't prevent, which is a "jump" in that ["renewal process"](https://en.wikipedia.org/wiki/Renewal_theory) and therefore delineates the "holding time" since the previous jump.
Here it's shown for the shortest durations whose cumulative probability is at least 95% along with select quantiles.

{insert plot 1}

{hr}

For a given positive maximum EB size {input MaxSize, default 12000}, we can calculate the throughput capacity offered by the successful EBs on an average g-chain.
If we optimistically assume that every EB that g doesn't prevent is both successful and full, then the average capacity will be MaxSize ÷ (N ÷ g) = {eval MaxSize ÷ (N ÷ g)} bytes per second.
Here it's shown for possible values of L from 1 to ⌈L×4÷3⌉.

{insert plot 2}

Also shown in orange is the average rate at which EBs are announced.
Note that as L increases or g decreases, the capacity decreases but the amount of announcements doesn't change---it's still one per 1/f=20 seconds.
MaxSize can be increased to bring the capacity back up, but that also proportionally increases the size of each announced EB.
It's therefore important to acknowledge that adversarial RBs are able to announce any EB they want, and the whole network will diffuse it---they can choose to always announce full EBs, even if no EB has succeeded for a long while.

Suppose the adversary controls a percentage of the total stake {input A, default 33, both a number input and a coupled slider} between 0 and 50%.
(If A is large, the adversary could severely reduce g well below f=5%, for example, by simply withholding their own blocks.
But whether to do so is that adversary's perogative, and so the variables can be tuned independently.)
This adversary leads each slot with a probability of φ<sub>f</sub>(A) = 1 - (1 - f)<sup>A</sup> = {let pA be 1 - 0.95^A}.
Thus, the ratio of the network utilization the adversary can steadily cause versus the average g-chain capacity is (N ÷ g) ÷ (1 ÷ φ<sub>f</sub>(A)) = {eval (N ÷ g) ÷ (1 ÷ pA)}---and that's even assuming the adversary is choosing to include certs in its RBs.
If they instead omit Leios certs from their RBs, then the ratio worsens by some factor like 1 ÷ (1 - A) to {eval ((N ÷ g) ÷ (1 - A)) ÷ (1 ÷ pA)}.

If the adversary is causing mempool fragmentation, then the _honest_ announced EBs could also be full even when no EBs are succeeding.
In the most extreme case, the ratio would worsen to (N ÷ g) ÷ (1 ÷ f) = {let frag be (N ÷ g) ÷ (1 ÷ f)} or even something like 1 ÷ (1 - A) times worse at {eval frag ÷ (1 - A)} if the adversary omits Leios certs in their RBs.

Three caveats.

- The 1 ÷ (1 - A) is a crude guesstimate.
  The actual multiplier depends on how much of the g-chain consists of adversarial blocks.
- The above inefficiency ratio calculations exclude the network utilization necessary for the EBs themselves (distinct from the transactions to which they refer) and the votes.
  Those exclusions are much smaller than full EBs, but not totally negligible---that is a forgivable shortcoming of the current draft.
- The above also ignores the fact that every SPO elected in a multi-leader slot announces an EB.
  That's an additional ~2.5% inefficiency excluded in the above calculations.

{hr}

Finally, a question related to how quickly the Mempools would need to be able to refill.
If EBs are succeeding too quickly, back-to-back, then TxSubmission might not be able to replenish the Mempools to saturate the unusually high density of successful EBs on the g-chain.

The following plot has x-axis from k=0 to k=30×L.
It plots the probability that there will be at most M additional EBs allowed by g within the k slots starting immediately after some jump.

{insert plot 3}

CIP-0164 recommends a Mempool containing enough transactions for two full EBs.
Thus, the M=1 curve captures the probability that a Mempool that was full before the initiating EB would suffice even if it wasn't refilled at all.
The M=2 curve, therefore, indicates how soon the Mempool would need to refill one EB's worth of transactions to avoid not being able to fill the third EB in a short timeframe.
The higher M curves would demand that much faster refilling.
