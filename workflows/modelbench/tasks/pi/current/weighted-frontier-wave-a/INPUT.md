# Exact task interface

Repository branch: `pi-core-consolidation`

Source commit: `3733305a2e85f57c91d669b7acaad47f5bee3299`

Verified sources:

- `TheoryLib/PiQuantitativeBlockHitting/T120T120WeightedNaturalScaleFrontier.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T121T121WeightedNaturalScaleCriterion.lean`
- `knowledge/pi/results/intermediate/20260823-moving-mesh-collision-haar-consumer.md`

Write `S_h(N)=sum_{n<N} exp(2*pi*i*h*x_n)`. The verified Jackson load is

```text
J(x,N,q) = (1/N) sum_{indices i: h_i != 0} |c_i| |S_{h_i}(N)|.
```

An empty interval of length `1/q` forces

```text
J(x,N,q) >= c0(q),   c0(q)=1/(3q)+2/(3q^3).
```

For `x_n=fract(10^n*pi)` and `q=10^k`, finding for every `k>=1` one `N>0`
with `J(x,N,q)<c0(q)` implies canonical V1. The older simultaneous pointwise
T19 premise implies this weighted premise, while a generic finite separator
shows the converse fails. No required fixed-pi estimate is known.

The parallel collision frontier assumes selected-block cell occupancies obey a
bound shaped like `sum_a n(a)^2 <= C*(L^2/q+L)` and derives Haar convergence;
that occupancy premise for pi is also open.

Every assigned task attacks a precise mathematical input below this interface.
No task proves V1 unless it actually proves the fixed-pi premise for every
decimal scale. No task may claim density, normality, or novelty.
