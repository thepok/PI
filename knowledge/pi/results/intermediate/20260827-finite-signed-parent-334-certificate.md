# Finite target-signed parent score at `q = 1000`, `A = 334`

Status: `experiment` (directed-interval replay passed); not yet
`machine-checked`.

Date: 2026-08-27 UTC

## Exact finite claim

For the actual decimal orbit of pi, the replay establishes the strict finite
inequality

\[
 \Re\operatorname{primitiveBoundaryFourierSum}(1000,334,10000)
 > \frac{47539}{2500}=19.0156.
\]

The outward-rounded interval obtained by the replay is

\[
19.0156236886870662490925062024612738870059063676813391373044
< \Re Z
<
19.0156236886870662490925062024612738870059063676813391373045.
\]

Thus the certified numerical margin above the rational threshold is greater
than

\[
2.36886870662490925065\cdot 10^{-5}.
\]

This is genuine target-signed Archimedean information about the fixed
constant pi. It is finite computation, not an all-scale source mechanism.

## Certificate chain

The replay is
[`workflows/experiments/t170_signed_parent_334_interval.py`](../../../workflows/experiments/t170_signed_parent_334_interval.py).
It uses only the Python standard library and checks the complete-file SHA-256
of the retained T17 prefix:

```text
77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684
```

T17 independently forces those 1,048,596 fractional decimal digits from an
exact rational Chudnovsky bracket. Its report and one-command regeneration are
in
[`library/t17/REPORT.md`](workstream-archive/pi-lacunary-near-return-sparsity/library/t17/REPORT.md).

T173 now independently machine-checks the particular 10,015-fractional-place
pi cylinder needed for this finite horizon, using 14,341 compact integer
Machin rows. This closes the prefix-trust and scaling rung inside Lean. The
claim in this memo nevertheless remains `experiment`: the outward-rounded
sine/cosine evaluation and its final score inequality are still replayed by
Python rather than accepted by the Lean kernel.

For each required orbit point, T170 reads a 145-digit suffix and therefore
encloses the fractional part between adjacent exact decimal rationals. It
then evaluates the T128 closed kernel, the exact zero coefficient, and the
T139 endpoint by:

- Machin alternating-series bounds for the geometric constant pi;
- outward-rounded 100-place decimal interval arithmetic;
- centered rational range reduction;
- 62-term sine and cosine Taylor sums with explicit Lagrange remainders;
- the machine-checked T128/T139 algebraic identities relating the kernel sum,
  endpoint, and primitive score.

The independently reproduced subintervals are:

```text
kernel sum  = 60.93394952154363990401217382081019287824732643874418...
alpha_1000  = 0.00228986707282197271475108592742915668866706016967...
endpoint Re = 0.00201570797489012915815107079803910878245600329746...
score Re    = 19.01562368868706624909250620246127388700590636768134...
```

Replay from the repository root:

```bash
bash knowledge/pi/results/intermediate/workstream-archive/pi-lacunary-near-return-sparsity/library/t17/reproduce.sh
python3 workflows/experiments/t170_signed_parent_334_interval.py
```

The first command regenerates and compares the exact pi-prefix artifacts; the
second performs the signed interval evaluation. The signed replay took about
73 seconds in the operator run.

## What this changes

The result demonstrates concretely that an actual-pi signed estimate can feed
the verified T148/T156 consumer. It is stronger information than the already
known finite occurrence of `334`, because it evaluates the complete primitive
score with its target phases and endpoint bookkeeping.

It does **not** establish a new occurrence: the previously certified digit
prefix already contains `334`, and all ten one-digit left extensions of that
suffix occur by start 14250. It also gives no recurrence, prescribed-child
selection, unbounded scale family, or proof of V1.

The next trust step is deliberately narrow: connect the T173 cylinder to a
compact kernel-checked directed trigonometric interval evaluator and prove the
same inequality in Lean. Until that full score theorem compiles and is
registered in the axiom audit, this note remains labeled `experiment`.
