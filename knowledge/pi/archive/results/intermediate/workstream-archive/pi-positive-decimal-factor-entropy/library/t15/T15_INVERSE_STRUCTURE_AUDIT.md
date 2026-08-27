# T15 source-pinned inverse-structure audit

Status: `literature-checked` on 2026-07-23 for the bounded corpus in
`SOURCE_MANIFEST.md`.

This is an applicability audit, not a proof about pi. `DOES NOT APPLY` means
that the cited result cannot be invoked from all the hypotheses and
quantifiers supplied by the indicated kernel-checked theorem. It does not say
that the cited theorem is false, that its missing hypothesis is false for pi,
or that no stronger result exists.

## 1. Immutable target and exclusions

The canonical statement is staged for replay as
`dependencies/problems/pi-positive-decimal-factor-entropy.txt` (copied from
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`), SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
It asks for one fixed `eta > 0` and one `N >= 1` such that every `n >= N`
satisfies `p_pi(n) >= 10^(eta*n)`. Nothing below asserts that statement or its
negation.

This audit deliberately does not repeat T5's direct-estimate survey. T5's
`DELTA_AUDIT.md` (SHA-256
`93089b4f44db9e295d1f8f560adf5b5b2922e624abfd084b92f6cfb8a0543129`)
and `SOURCE_MANIFEST.md` (SHA-256
`a1d9bbac1e5043476c3f2053ec4cdf2c65179acfee63ee03c1f3c397547bdb05`)
already audit direct discrepancy and metric lacunary estimates, pair
correlation, BBP/Bailey-Crandall routes, and irrationality-measure input.
Those sources and conclusions are excluded here. The present corpus is
restricted to structural inverse mechanisms: large spectra, dissociated
(lacunary) frequency families, almost-periods of convolutions, and
additive-energy structure.

## 2. Exact kernel inputs

Write

```text
S(q,m) = sum_(0 <= j < m) exp(2*pi*i*q*frac(10^j*pi)).
```

This is only notation for the `piOrbitSum q m` appearing in the checked
files; it introduces no new estimate.

### T10 isolated resonance

Source: `dependencies/t10/T10ScaleAdaptiveOrbitFourier.lean` (the staged copy
of `knowledge_library/t10/T10ScaleAdaptiveOrbitFourier.lean`), SHA-256
`390946b9d5bc2f3d964b28eb98293db7c3268ad3dfe90aad2f75d4fef37fb4b8`.
Exact locator: theorem
`piFailureC1_implies_arbitrarily_large_scale_resonance`, lines 435-456.

Conditional on the literal negation of C1, the exact conclusion is

```text
forall B : Real, 0 <= B -> forall N : Nat, 1 <= N ->
  exists n k M H : Nat, exists h : Int,
    N <= n
    and M = 10^n
    and 4^k <= M
    and H = M / 2^(k+1)
    and h != 0
    and |h| < H
    and B*M < |S(h,M)|^2.
```

Here `B` and the lower scale `N` precede every witness. The theorem supplies
one coefficient at the resulting scale. It does not make `h`, `k`, or the
phase of `S(h,M)` persistent when `B` or `N` changes. Its normalized
coefficient only satisfies

```text
|S(h,M)|/M > sqrt(B/M).
```

Because `M` is selected after `B`, T10 does not supply a positive lower bound
for this normalized coefficient that is independent of the witness.

### T13 descendant resonance

Source: `dependencies/t13/T13AutocorrelationAmplification.lean` (the staged
copy of `knowledge_library/t13/T13AutocorrelationAmplification.lean`), SHA-256
`0550764bdae3e9c19ddf1ea76321c674046b2cd674f825007ca5bc6652e95ea1`.

The exact Pareto form is theorem
`piFailureC1_implies_growing_cutoff_pareto_quantifiers`, lines 275-327. It
retains all T10 witnesses and adds

```text
L = 2^n,  1 <= r <= M-L,  L <= M-r,
descendant frequency d = h*(10^r-1),
Re S(d,M-r) greater than the displayed Pareto average.
```

The clean unbounded descendant form is theorem
`piFailureC1_implies_growing_remainingLength_resonance`, lines 333-400:

```text
forall C : Real, 0 <= C -> forall N : Nat, 1 <= N ->
  exists n k M H L r : Nat, exists h : Int,
    N <= n
    and M = 10^n
    and 4^k <= M
    and H = M / 2^(k+1)
    and h != 0
    and |h| < H
    and (2*C+2)*M < |S(h,M)|^2
    and L = 2^n
    and 1 <= r <= M-L
    and L <= M-r
    and C < Re S(h*(10^r-1),M-r).
```

Thus `C` precedes the witnesses and the child length grows, but the child
bound is absolute rather than normalized by `M-r`. T13 gives no child scale
`k'`, no child bandwidth `H'`, no assertion that
`|h*(10^r-1)| < H'`, and no requirement that `M-r` be a power of ten. It
also gives one selected lag per witness, not a positive-density family of
phase-aligned lags. These absent clauses are not inferred silently below.

## 3. Applicability standard

For this audit, a result is marked `APPLIES` to T10 or T13 only if its
hypotheses follow from the complete displayed conditional conclusion without
adding a density, discretization, energy, phase, or compatibility premise,
and if its conclusion yields nontrivial structure beyond the one coefficient
already supplied. A result that can be applied only after inventing an
unproved finite model, or whose conclusion is vacuous for a singleton large
spectrum, is marked `DOES NOT APPLY`.

The following matrix records the structural data actually available.

| Structural datum | Full T10 | Full T13 |
|---|---|---|
| Ambient object | One length-`M` empirical orbit on the circle; no finite-group model is supplied. | Parent orbit plus one child orbit of length `M-r`; no common finite-group model is supplied. |
| Size normalization | `|S|^2 > B*M`, with `M` chosen after `B`; no fixed positive Fourier density. | Parent as at T10; child only `Re S > C`, with child length chosen after `C`. |
| Number of controlled frequencies | One `h` for each witness. | One parent `h` and one descendant `h*(10^r-1)` for each witness. |
| Cross-witness phase alignment | None; T10 retains only the norm. | Child real part is positive for that witness, but there is no alignment across different `C`, `N`, or lags. |
| Frequency compatibility | Parent satisfies `0 < |h| < H`. | No descendant bandwidth or scale condition; `M-r` need not be `10^m`. |
| Additive energy or small doubling | None. | None; a single autocorrelation selected by averaging is not a normalized additive-energy hypothesis. |

## 4. Audited inverse results

Every retained result receives a separate verdict against both complete
quantifier systems.

### L1. Lee, Theorem 3.3 (Chang large-spectrum covering)

Exact locator: James R. Lee, *Covering the large spectrum and generalized
Riesz products*, arXiv:1508.07109v2, Theorem 3.3, printed/arXiv PDF p. 8.
The source defines `Delta_G` as nonnegative densities of mean one on a finite
abelian group and `Spec_delta(f) = {gamma: |fhat(gamma)| > delta}`. The theorem
says this spectrum is `d`-covered by signed sums from at most
`4 Ent_mu(f)/delta^2` generators.

T10 verdict: **DOES NOT APPLY.** T10 supplies neither a finite abelian group
nor a density `f` and threshold `delta` independent of its witness. Even after
an extra discretization, T10 supplies one large character. A singleton
spectrum is already one-covered, so Chang's conclusion creates no relation
between the frequencies arising for different `B` or `N`. The first decisive
missing hypothesis is a nontrivial large spectrum for one common finite
probability density at a controlled positive normalized threshold.

T13 verdict: **DOES NOT APPLY.** Parent and descendant sums have different
lengths and witness-dependent frequencies, and T13 supplies no common finite
group/density in which they form a large spectrum. In particular it gives no
signed-span compatibility between descendants from different witnesses and
no child bandwidth. The first decisive missing hypothesis is multi-frequency
compatibility in one common spectrum; the unnormalized child inequality does
not provide it.

### L2. Shkredov, Theorem 1.2 (large coefficients on a dissociated set)

Exact locator: I. D. Shkredov, *Some applications of W. Rudin's inequality to
problems of combinatorial number theory*, arXiv:1002.1886v1, Theorem 1.2,
printed/arXiv PDF p. 2, formula (2). If `S` has density `delta` in a finite
abelian group and `Lambda` is dissociated, it bounds the sum over `Lambda` of
squared Fourier coefficients of `1_S` by an absolute constant times
`|S|^2 log(1/delta)`.

This result is retained for its inverse large-spectrum consequence: at a
fixed coefficient threshold it limits how many mutually dissociated large
coefficients a positive-density set can have. The underlying direct Rudin
moment theorem is not audited here; doing so would duplicate T5's direct
lacunary-estimate category.

T10 verdict: **DOES NOT APPLY.** T10 has no finite set `S`, ambient group, or
controlled density `delta`; identifying its orbit with a set of cells would
require an unproved discretization and multiplicity analysis. It also gives
only one frequency, so the theorem's many-frequency energy control yields no
new inverse structure. The first unmet hypothesis is a positive-density
finite set carrying a family of large dissociated coefficients.

T13 verdict: **DOES NOT APPLY.** T13's child uses a different length and
multiplier and is not a second coefficient of one fixed set `S` in one group.
There is no density bound, common support, or dissociated family of many
large descendants. The first unmet hypothesis is common-support
frequency compatibility, before any phase or density conclusion can be
drawn.

### A1. Croot-Sisask, Proposition 1.1 (local L2 almost-periodicity)

Exact locator: Ernie Croot and Olof Sisask, *A probabilistic technique for
finding almost-periods of convolutions*, arXiv:1003.2978v2, Proposition 1.1,
printed/arXiv PDF p. 3. Given finite sets `A,B,S` in a group with
`|B*S| <= K|B|`, it produces a quantitatively large `T subset S` such that
every `t in T*T^{-1}` is an `L2` almost-period of `1_A*1_B` with the displayed
`epsilon^2 |A||B|^2` error.

T10 verdict: **DOES NOT APPLY.** T10 supplies no finite sets `A,B,S`, no
convolution encoding its orbit sum, and especially no small-growth condition
`|B*S| <= K|B|`. One large Fourier coefficient does not by itself imply that
small-growth hypothesis. The first decisive missing hypothesis is additive
or multiplicative density/small growth for a finite model of the orbit.

T13 verdict: **DOES NOT APPLY.** A selected autocorrelation lag is not a large
set `T*T^{-1}` of almost-periods and does not imply the proposition's
small-growth premise. T13 also gives no mechanism making the almost-periods
respect descendant multiplication `h -> h*(10^r-1)` or a child bandwidth.
The first missing hypothesis is a dense family of almost-periods generated
from a controlled convolution, not one selected lag.

### E1. Shao, Theorem 1.4 (Balog-Szemeredi-Gowers)

Exact locator: Xuancheng Shao, *Large values of the additive energy in R^d
and Z^d*, arXiv:1308.2247v1, Theorem 1.4, printed/arXiv PDF p. 2. The source
normalizes additive energy by `|A|^3`. If a finite subset of an abelian group
has normalized energy at least `1/K`, the theorem produces a polynomially
large subset with polynomially bounded doubling.

T10 verdict: **DOES NOT APPLY.** T10 gives a Fourier coefficient of a circle
orbit, not a finite set with at least `|A|^3/K` exact additive quadruples.
Using the finite-group identity between fourth Fourier moments and additive
energy would first require an exact character-preserving finite model of the
orbit coefficient, with multiplicities and approximation errors controlled;
T10 supplies no such model. Even after that separate transfer, a
witness-dependent single coefficient would still need a scale-uniform
normalized fourth-moment contribution. The first unmet hypothesis is
scale-uniform normalized additive energy, preceded by the missing exact
finite-model transfer.

T13 verdict: **DOES NOT APPLY.** One parent coefficient and one child
coefficient at a different support length do not count exact additive
quadruples of one set. The child lower bound `Re S > C` is unnormalized, and
`M-r` is selected after `C`, so it supplies no fixed energy density. The
first unmet hypothesis is high normalized energy on one common finite set;
frequency compatibility is absent as well.

### E2. Shao, Theorem 2.1 (low-rank progression from excess energy)

Exact locator: the same pinned source, Theorem 2.1, printed/arXiv PDF p. 4.
For finite subsets `A_1,...,A_k` of a torsion-free abelian group, it assumes
their `k`-fold additive energy exceeds the corresponding Euclidean-ball
benchmark by `epsilon |X|^(k-1)` and concludes that a positive proportion of
their union lies in a proper progression of rank at most `d` and comparable
size.

T10 verdict: **DOES NOT APPLY.** T10 provides none of the finite torsion-free
sets, the exact `k`-term relation count, or the fixed positive excess
`epsilon |X|^(k-1)`. A witness-dependent single coefficient cannot supply
the benchmark inequality. The first unmet hypothesis is positive normalized
excess additive energy, stronger than the missing BSG premise above.

T13 verdict: **DOES NOT APPLY.** T13's descendant multiplier and remaining
length do not define the common sets `A_i` required by the theorem, and the
absolute child lower bound gives no fixed `epsilon` excess. The first unmet
hypothesis is again normalized energy; even a resulting progression would
need an additional theorem to enforce the T10 child bandwidth and base-ten
descendant map.

## 5. Verdict matrix

| ID | Structural route | T10 full quantifiers | T13 full quantifiers | First decisive absent datum |
|---|---|---|---|---|
| L1, Lee Theorem 3.3 | Concentrated Fourier energy / large spectrum | **DOES NOT APPLY** | **DOES NOT APPLY** | One common positive-threshold multi-frequency spectrum. |
| L2, Shkredov Theorem 1.2 | Dissociated/lacunary large-spectrum energy | **DOES NOT APPLY** | **DOES NOT APPLY** | A common finite support of controlled density with many coefficients. |
| A1, Croot-Sisask Proposition 1.1 | Approximate periodicity | **DOES NOT APPLY** | **DOES NOT APPLY** | Small growth/density and a convolution model; T13 has only one lag. |
| E1, Shao Theorem 1.4 | Additive energy to small doubling | **DOES NOT APPLY** | **DOES NOT APPLY** | Scale-uniform normalized exact additive energy. |
| E2, Shao Theorem 2.1 | Energy to low-rank progression | **DOES NOT APPLY** | **DOES NOT APPLY** | Positive normalized excess energy in common torsion-free sets. |

## 6. Pinned structural frontier

For this bounded corpus, no audited inverse theorem applies to the complete
T10 or T13 quantifiers. The common obstruction is not a missing direct
estimate of the kind audited in T5. It is the absence of a coherent
structural hypothesis:

1. T10 permits the normalized coefficient `|S|/M` to tend to zero because
   the witness scale follows `B`.
2. T10 gives one frequency and no cross-witness phase alignment.
3. T13 gives one descendant per witness, with an absolute rather than
   length-normalized bound.
4. T13 supplies no descendant bandwidth, no base-ten sample-size
   compatibility, and no common support on which parent and child are a large
   spectrum.
5. Neither theorem supplies positive-density almost-periods or normalized
   additive energy.

An inverse route would become checkable after proving at least one genuinely
new premise of the following type: a fixed positive normalized threshold for
many compatible frequencies in one scale model; a positive-density,
phase-aligned family of T13 lags whose descendants remain in an admissible
bandwidth; or a finite model with scale-uniform normalized additive energy
and a proved transfer back to the ordinary orbit. None of these premises is
claimed for pi here.

The conclusion is a `literature-checked` negative applicability result for
the declared corpus, not an exhaustive no-go theorem and not an unconditional
claim about pi.
