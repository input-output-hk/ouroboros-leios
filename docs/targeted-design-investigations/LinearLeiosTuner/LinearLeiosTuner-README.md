LeiosTuner.html is a interactive Dynamic HTML calculator with two inputs.

Its title is Linear Leios Tuner. Its introduction is:

> An interactive calculator for ballparking best-possible EB success rate and overall Leios capacity for various values of L and MaxSize, where L=3×L_hdr + L_vote + L_diff.

The first section is titled Arrival rate of inter-RB gaps ≥ L (at 5% active slot coefficient).
Its input is a simple integer 2≤L≤200, default of 14 (it's both a number input and a coupled slider).
Its output is a step plot portraying the probability mass holding times in a renewal process defined by L (truncating x-axis after 95% cumulative).
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

The second section is titled Theoretical average capacity (with 100% stake participating, max EBs, succeed if L gap).
Its input is a positive integer MaxSize, defaulting to 1000 (just a number input---no slider).
Its output is another step plot, showing MaxSize divided by the mean holding time for all run lengths from 2 to ⌈L×4÷3⌉, with the value for L highlighted.
