# Same-mesh occupancy does not control the Jackson load

Status: `proof sketch`

Date: 2026-08-24 UTC

Fix `q >= 2` and `N=2q`. Compare the samples

```text
A_n = n/(2q),
B_(2a) = B_(2a+1) = a/q  for 0 <= a < q.
```

On the `q`-cell mesh both have exactly two points per cell and hence identical
occupancy energy

```text
sum_a n(a)^2 = 4q = N^2/q.
```

The uniform `2q`-grid `A` has zero exponential sums at every nonzero frequency
in the actual Jackson support, so its weighted load is zero. For `B`, the
normalized exponential sum is one exactly when `q` divides the frequency.
Inside the support only `h=+q` and `h=-q` contribute. The proposed exact mass

```text
w_q(q) = 5/(6q) - 1/(3q^3)
```

therefore gives

```text
J_q(B;2q) = 5/(3q) - 2/(3q^3)
          > 1/(3q) + 2/(3q^3).
```

Consequently, even an exact same-mesh occupancy vector does not determine or
upper-bound the Jackson load at that mesh scale. An uncentered estimate shaped
only as `sum n(a)^2 <= C*(N^2/q+N)` cannot directly supply the required
same-scale centered Jackson-kernel estimate.

Scope is essential: this does not refute the reviewed full moving-mesh
consumer, whose pseudo-orbit and asymptotic hypotheses force Haar convergence.
It refutes only a direct occupancy-vector-alone implication with Jackson order
tied to the same mesh. It is not a counterexample involving pi.

V1 remains open.
