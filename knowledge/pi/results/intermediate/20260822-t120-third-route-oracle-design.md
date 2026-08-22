# T120 controller-owned third-route oracle design

Status: `experiment` infrastructure design. This is not a finite PI result and
does not authorize any production index.

The recommended third route for PREW13 is a one-shot common-multiple integer
lift of the original BBP bracket, restricted to `N=0..10`. It is independent
of S1's collapsed quadratic term and S2's normalized rational-pole accumulator.

For each `k`, define integer denominators

- `d1(k)=16^k(8k+1)` with coefficient `4`;
- `d4(k)=16^k(8k+4)` with coefficient `-2`;
- `d5(k)=16^k(8k+5)` with coefficient `-1`;
- `d6(k)=16^k(8k+6)` with coefficient `-1`.

For an inclusive interval `[u,v]`, let `L(u,v)` be the least common multiple
of every `dr(k)` in that interval and set

`U(u,v)=sum_(k=u)^v (4L/d1(k)-2L/d4(k)-L/d5(k)-L/d6(k))`.

`reduce(z,D)` requires `D>0`, divides by `gcd(abs(z),D)`, and normalizes zero
to `0/1`. For each record `N`, independently compute

- `Q_N = reduce(10^N U(0,7N), L(0,7N))`;
- `F_N = reduce(10^(N+1) U(7N+1,7N+7), L(7N+1,7N+7))`;
- `S_N = reduce(10^(N+1) U(0,7(N+1)), L(0,7(N+1)))`.

Writing reduced `Q=(A,D)` and `F=(C,E)`, reconstruct exactly the T118 data:
`H=gcd(D,E)`, `d=D/H`, `e=E/H`, `X=10Ae+Cd`,
`k=gcd(abs(X),H*d)`, `W=H*d*e/k`, and `Y=X/k`. Require `(Y,W)=S_N`, then
take the Euclidean remainder `R=Y mod W` and `cell=floor(10R/W)`. Emit only
`n,r,w,cell`.

The controller accepts only the tiny half-open shards `[7,11)`, `[0,2)`, and
`[2,7)` in that order. Every shard reconstructs from term zero with no prior
artifact, checkpoint, candidate source, expected arithmetic, or persistent
state. The route forbids `Fraction`, rational-pair accumulation, the T98
quadratic numerator, endpoint subtraction for `F`, S1/S2 imports, lookup tables,
shared arithmetic, and production ranges.

Hidden tests must cover omitted/doubled endpoints, wrong powers of ten, all
coefficient/sign/offset mutations, wrong forcing bands, non-LCM aggregation,
bad gcd/zero normalization, swapped `d,e`, missing leading `10` in `X`,
truncating instead of Euclidean remainder, `%10` cells, boundary cells, shard
gaps/reordering/state contamination, and jobs containing expected values.

This route is suitable only as an independent controller oracle for the frozen
tiny shards. Agreement remains finite workflow evidence under claim label
`experiment`; it proves nothing about later PI digits.
