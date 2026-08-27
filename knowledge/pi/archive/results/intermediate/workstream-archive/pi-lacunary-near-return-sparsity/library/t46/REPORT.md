# T46: irrationality packing on one genuine T26/T38 stratum

Status: `proof sketch`.

This is a local necessary-condition audit under the temporary assumption that
canonical A1 fails. It is not a proof of that assumption, its negation, C1,
FSFS, adjacent compatibility, or cancellation at a fixed multiple of `pi`.
The only formal premises are the vendored kernel-checked T26 and T38 files.
The only external arithmetic premise is the source-pinned irrationality
measure theorem in Section 3. T40 and T43 are not premises.

## 1. Immutable statement and interpretation

The byte-identical `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

Its canonical question is

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \ \forall n\geq n_0\ \exists N\geq1:
 \quad AnQ_\pi(n,N)\leq N^2,                         \tag{1.1}
\]

where `Q_pi` counts ordered pairs, includes the diagonal, and uses strict
circle distance below `10^(-n)`. The local statement has no external original
source URL; its provenance is preserved verbatim at line 5. This note does not
replace eventual `n` by infinitely many `n`, prescribe `N`, remove the
diagonal, use unordered pairs, or change `pi`, base 10, or circle distance.

## 2. Kernel-checked inputs

The vendored inputs and exact locators used here are:

| File | SHA-256 | Locators |
|---|---|---|
| `T26SharedResonanceChain.lean` | `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2` | chain fields and node formulas, lines 125-152; density, error, and monotonicity, lines 175-200; literal failure theorem and all cutoffs, lines 285-311 |
| `T38FixedStratumFejerSpike.lean` | `853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014` | strata and cardinality, lines 34-105; radius and order, lines 329-394; exact FSFS target, lines 396-412; Fejer expansion, lines 622-676 |

T26's conclusion is necessary-only. T38 defines FSFS as a hypothesis. This
note uses neither predicate as an established statement about `pi`.

## 3. Pinned irrationality theorem

The retained primary source is Doron Zeilberger and Wadim Zudilin, *The
irrationality measure of pi is at most 7.103205334137...*, Moscow Journal of
Combinatorics and Number Theory 9 (2020), no. 4, 407-419.

- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher page: <https://msp.org/moscow/2020/9-4/p06.xhtml>
- PDF URL: <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- `zeilberger-zudilin-2020.pdf` SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- `zeilberger-zudilin-2020.txt` SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`

Exact theorem locators are printed p. 407, PDF page 2, retained text lines
27-34 for the definition and eventual quantifiers of irrationality measure;
printed p. 407, PDF page 2, lines 22-23 and 40-42 for the announced bound; and
the `World record` paragraph on printed p. 418, PDF page 13, lines 676-691 for

\[
 \mu(\pi)\leq
 7.10320533413700172750577342281\ldots <8.             \tag{3.1}
\]

Taking a positive epsilon that raises the exponent to 8 in the definition
gives exactly the following consequence, with no numerical cutoff claimed:

\[
 \exists Q_8\in\mathbb N_{\geq1}\ \forall q\in\mathbb N,
 \ q\geq Q_8\ \forall p\in\mathbb Z:
 \quad |\pi-p/q|>q^{-8}.                                \tag{3.2}
\]

For such `q`, choosing a nearest integer `p` to `q*pi` gives

\[
 \boxed{\ \|q\pi\|_{\mathbb R/\mathbb Z}>q^{-7}.\ }   \tag{3.3}
\]

The existential `Q8` is retained throughout; it is never assigned a value.

## 4. A genuine consecutive T26 pair

Temporarily assume the literal negation of (1.1). T26, lines 296-311, gives
an `A>=1`; for every `n0>=1` it gives `n>=n0`, `n>=1`; and for every requested
depth `d` it gives `N,r,h` and one chain. Select the source cutoff `Q8` from
(3.2), set

\[
 d:=Q_8\geq1,\qquad k:=d-1,                             \tag{4.1}
\]

and apply T26 at that depth. Its complete parameter substitution is

\[
 \begin{aligned}
 D&:=131072A^2n^2,\\
 D_i&:=\operatorname{densityDenominator}(D,i),\\
 K&:=2D_d^2,\\
 L&:=\operatorname{iterationLengthThresholdAux}(D,1,K,1,d),\\
 N&:=16AnL,\qquad M:=N-r,                               \tag{4.2}
 \end{aligned}
\]

with

\[
 1\leq r\leq N-1,\qquad 1\leq h\leq256An.             \tag{4.3}
\]

Write the chain shifts as `s_0,...,s_(d-1)`. They are distinct, each is at
least 1, and none equals `r`. At node `i<=d`, put

\[
 \begin{aligned}
 M_i&:=N-r-\sum_{t<i}s_t,\\
 C_i&:=h(10^r-1)\prod_{t<i}(10^{s_t}-1),\\
 \beta_i&:=C_i\pi,\qquad \tau_i:=\frac1{8D_i^2}.       \tag{4.4}
 \end{aligned}
\]

T26 retains, at every such node, the actual consecutive-chain resonance

\[
 \frac{M_i}{D_i}<
 \left|\sum_{x=0}^{M_i-1}e(\beta_i10^x)\right|,
 \qquad e(y):=\exp(2\pi i y).                            \tag{4.5}
\]

The pair used below is the final genuine consecutive pair `k=d-1` and `d`.
Set

\[
 C:=C_k,
 \qquad U:=10^{s_k}-1.                                  \tag{4.6}
\]

Then `beta_k=C*pi` and `beta_d=UC*pi` by direct comparison of the two prefix
products. There is no selected or synthetic coefficient here.

Every displayed base-ten factor in `C` is at least 9. There is one initial
factor `10^r-1` and exactly `k=d-1` preceding shift factors, so

\[
 C\geq9^d\geq d=Q_8.                                   \tag{4.7}
\]

The elementary inequality `9^d>=d` follows by induction for `d>=1`. Likewise

\[
 U\geq9.                                                \tag{4.8}
\]

No compatibility of the two nodewise inverse alternatives is used.

## 5. Explicit admissibility of the minimal stratum

T26's final-residual field and prefix monotonicity give

\[
 M_d=M-\sum_{t<d}s_t\geq K,
 \qquad M_k\geq M_d.                                   \tag{5.1}
\]

Since `D>=131072` and density denominators are positive and nondecreasing,

\[
 K=2D_d^2\geq2D^2\geq
 2(131072)^2=34359738368>1.                             \tag{5.2}
\]

T38 defines `commonDepth=min(M_k,M_d)`. Therefore

\[
 \operatorname{commonDepth}(\mathrm{chain},k)
 =M_d\geq K\geq2.                                      \tag{5.3}
\]

Choose the smallest possible nonempty T38 stratum,

\[
 \ell:=1<\operatorname{commonDepth}(\mathrm{chain},k). \tag{5.4}
\]

T38's definitions and cardinality theorem give, without a pigeonhole step,

\[
 \operatorname{denominatorStratum}(1)=\{(0,1)\},
 \qquad |\operatorname{denominatorStratum}(1)|=1,       \tag{5.5}
\]

and its unique denominator is

\[
 Q_0=10^1-10^0=9.                                      \tag{5.6}
\]

Thus the stratum is legal and nonempty independently of FSFS.

## 6. Exact T38 radius, order, and target

Unfold the node error as

\[
 E_i:=\operatorname{inverseError}(\tau_i)
 =\frac{\arccos(\tau_i)}{2\pi}.                         \tag{6.1}
\]

Since `D_i>=1`, one has `0<tau_i<=1/8<1/2`. Monotonicity of `arccos` and
`arccos(1/2)=pi/3` give

\[
 E_i>\frac16.                                           \tag{6.2}
\]

At `ell=1`, T38's radius is exactly

\[
 \begin{aligned}
 \delta
 &=\min\left\{E_k,\frac{E_d}{U},\frac1{2U10}\right\}\\
 &=\boxed{\frac1{20U}}.                                \tag{6.3}
 \end{aligned}
\]

Indeed `1/(20U)<1/6<E_k` and `1/(20U)<1/(6U)<E_d/U`.
Consequently every remaining cutoff is integral and explicit:

\[
 \boxed{R:=\lceil\delta^{-1}\rceil=20U\geq180.}        \tag{6.4}
\]

T38's analytic FSFS inequality on this stratum would be

\[
 \boxed{
 T:=\frac{1}{4R\delta^2}=\frac R4=5U
 <F_{R-1}(9C\pi)=:E.}                                  \tag{6.5}
\]

Equation (6.5) is the target to test, not an assumed premise.

## 7. Complete Fejer-weighted transported-frequency multiset

For the convention in T38, the Fejer identity gives

\[
 E=\sum_{u=-(R-1)}^{R-1}w_u e(\lambda_u\pi),
 \qquad
 w_u:=1-\frac{|u|}{R},\qquad
 \lambda_u:=9Cu.                                       \tag{7.1}
\]

This is the complete signed support `|u|<=R-1`, including `u=0`; no endpoint
of weight zero has been added. Its total weight is

\[
 \sum_uw_u=R.                                           \tag{7.2}
\]

Because `9C>0`, all integer-frequency equalities are classified by

\[
 \lambda_u=\lambda_v\iff u=v.                           \tag{7.3}
\]

The source theorem implies that `pi` is irrational, so phase equality modulo
one has the same classification:

\[
 e(\lambda_u\pi)=e(\lambda_v\pi)\iff u=v.              \tag{7.4}
\]

For ordered pairs, all equal-difference multiplicities are also complete:

\[
 \lambda_u-\lambda_v=9C(u-v),                           \tag{7.5}
\]

and two ordered pairs have equal frequency difference iff their index
differences `u-v` agree. For signed difference `d`, the unweighted
multiplicity is `2R-1-|d|` for `|d|<=2R-2` and zero otherwise.

## 8. Exact weighted multiplicities and zero difference

Extend `w_u` by zero outside `[-R+1,R-1]` and define

\[
 A_R(d):=\sum_{u\in\mathbb Z}w_uw_{u+d}\quad(d\geq0).  \tag{8.1}
\]

The zero-difference contribution is exactly

\[
 \boxed{S_2:=A_R(0)=\sum_uw_u^2=\frac{2R^2+1}{3R}.}    \tag{8.2}
\]

For every possible nonzero absolute difference,

\[
 \boxed{
 A_R(d)=
 \begin{cases}
 \dfrac{4R^3+2R-6Rd^2+3d^3-3d}{6R^2},
     &1\leq d\leq R-1,\\[6pt]
 \dfrac{(2R-d)^3-(2R-d)}{6R^2},
     &R\leq d\leq2R-2.
 \end{cases}}                                           \tag{8.3}
\]

To verify (8.2)-(8.3), multiply the weights by `R`. The generating polynomial
of `R-|u|` is `(1+z+...+z^(R-1))^2`; hence `R^2 A_R(d)` is the coefficient of
`z^(2R-2-d)` in

\[
 (1+z+\cdots+z^{R-1})^4=\frac{(1-z^R)^4}{(1-z)^4}.      \tag{8.4}
\]

Coefficient extraction gives (8.3). It also gives the consistency identity

\[
 S_2+2\sum_{d=1}^{2R-2}A_R(d)=R^2.                     \tag{8.5}
\]

Thus the diagonal has been isolated exactly, rather than hidden in a crude
`R^2` count. The formulas also show `A_R(d)` decreases with `d`: in the first
range the successive difference has numerator
`3(4Rd+2R-3d^2-3d)>0`, and in the second range it is
`(2R-d)(2R-d-1)/(2R^2)>0`.

## 9. Exact pair expansion and irrationality substitution

The Fejer kernel is real and nonnegative, so squaring (7.1) and grouping all
ordered pairs by `d=|u-v|` gives the exact identity

\[
 \boxed{
 E^2=S_2+2\sum_{d=1}^{2R-2}A_R(d)\cos(2\pi t_d),
 \qquad t_d:=\|9Cd\pi\|_{\mathbb R/\mathbb Z}.}         \tag{9.1}
\]

For each `d>=1`, set `q_d:=9Cd`. Equations (4.7) and (3.2) imply

\[
 q_d\geq9C\geq Q_8,                                    \tag{9.2}
\]

so the source theorem applies to every distinct transported-frequency pair,
with no small-denominator exception:

\[
 \boxed{t_d>(9Cd)^{-7}.}                                \tag{9.3}
\]

Since cosine decreases on `[0,1/2]`, this gives the parameter-only bound

\[
 \boxed{
 E^2<U_{\rm pt}:=S_2+2\sum_{d=1}^{2R-2}A_R(d)
 \cos\left(\frac{2\pi}{(9Cd)^7}\right).}               \tag{9.4}
\]

This is a very small improvement over the trivial height `R^2`, not a
cancellation theorem.

## 10. Complete 10-adic and dyadic packing split

Every `d` in (9.1) has the unique decomposition

\[
 d=10^am,\qquad a\geq0,\quad m\geq1,\quad10\nmid m.     \tag{10.1}
\]

Here `a` is explicitly the largest power of 10 dividing `d`; no prime
valuation identity is being assumed for the composite base 10. For `s>=2`,
define, for any `x` on the circle, the disjoint distance shell

\[
 \mathcal H_{a,s}(x):=\left\{m:
 \begin{array}{l}
 10\nmid m,\quad1\leq10^am\leq2R-2,\\
 2^{-(s+1)}\leq\|10^amx\|<2^{-s}
 \end{array}\right\}.                                  \tag{10.2}
\]

The actual shell is `H_(a,s)(9C*pi)`. These shells partition every term with
positive cosine, because
`cos(2*pi*t)>0` exactly for `0<=t<1/4` on `[0,1/2]`. Terms outside the shells
are nonpositive and may be discarded only for an upper bound.

Put `q0:=9C` and encode all finite exponent-7 constraints arising from the
transported differences by

\[
 \mathcal X:=\left\{x\in\mathbb R/\mathbb Z:
 \|dx\|>(q_0d)^{-7}\text{ for every }1\leq d\leq2R-2
 \right\}.                                               \tag{10.3}
\]

The actual point `x=q0*pi` belongs to `X` by (9.3).

For a fixed active valuation `a` satisfying `10^a<=2R-2`, put

\[
 M_a:=\left\lfloor\frac{2R-2}{10^a}\right\rfloor,
 \qquad L_a:=M_a-\left\lfloor\frac{M_a}{10}\right\rfloor. \tag{10.4}
\]

Thus `L_a` is the exact number of permitted primitive `m`. There are two
different lower bounds, which must not be conflated. The individual distance
bound is

\[
 \rho_a:=\bigl(q_0 10^aM_a\bigr)^{-7},\qquad
 \|10^amx\|>(q_0 10^am)^{-7}\geq\rho_a
 \quad(x\in\mathcal X).                                \tag{10.5}
\]

When `L_a>=2`, the pair-separation bound is

\[
 \eta_a:=\bigl(q_0 10^a(M_a-1)\bigr)^{-7}.              \tag{10.6}
\]

Indeed the defining constraint of `X`, applied to
`d=10^a|m-m'|`, gives for distinct permitted `m,m'`

\[
 \|10^a(m-m')x\|>\eta_a\quad(x\in\mathcal X).           \tag{10.7}
\]

Each shell in (10.2) is two circle arcs, each of length `2^(-(s+1))`.
Packing points separated by more than `eta_a` therefore gives, for `L_a>=2`,

\[
 |\mathcal H_{a,s}(x)|\leq
 B_{a,s}:=\min\left\{L_a,
 2\left\lceil\frac{2^{-(s+1)}}{\eta_a}\right\rceil
 \right\}.                                               \tag{10.8}
\]

For `L_a=1`, define `B_(a,s)=1`. A shell is empty when
`2^(-s)<=rho_a`, by the individual bound (10.5), so only finitely many `s`
occur. If

\[
 m_j:=j+\left\lfloor\frac{j-1}{9}\right\rfloor,         \tag{10.9}
\]

then `m_j` is the `j`-th positive integer not divisible by 10. Monotonicity of
`A_R` gives the fully weighted shell inequality

\[
 \boxed{
 \sum_{m\in\mathcal H_{a,s}(x)}A_R(10^am)
 \leq\sum_{j=1}^{B_{a,s}}A_R(10^am_j).}                 \tag{10.10}
\]

Equation (10.10) holds uniformly for every `x` satisfying the finite
transported-difference constraints in (10.3). It is a useful coarse
per-valuation packing inequality. It is not declared optimal, because it
discards simultaneous constraints between different shells and different
valuations.

The strongest bound justified by all finite exponent-7 constraints arising
from transported differences in this Fejer support can now be written
exactly, without that relaxation. Define the complete positive-shell weighted
packing envelope

\[
 \boxed{
 \begin{aligned}
 U_{\rm pack}^{\sharp}
 &:=S_2+2\sup_{x\in\mathcal X}
 \sum_{\substack{1\leq d\leq2R-2\\\|dx\|<1/4}}
 A_R(d)\cos(2\pi\|dx\|)\\
 &=S_2+2\sup_{x\in\mathcal X}
 \sum_{a:\,10^a\leq2R-2}\sum_{s\geq2}
 \sum_{m\in\mathcal H_{a,s}(x)}
 A_R(10^am)\cos(2\pi\|10^amx\|).
 \end{aligned}}                                         \tag{10.11}
\]

The discarded terms are nonpositive, so

\[
 \boxed{E^2\leq U_{\rm pack}^{\sharp}.}                \tag{10.12}
\]

This is the strongest upper envelope that uses the full simultaneous
arithmetic-progression structure and every pair-difference consequence (9.3)
within `1<=d<=2R-2`, then discards only nonpositive cosine terms. The second
line of (10.11) is its complete 10-adic and dyadic decomposition, while
(10.5)-(10.10) give directly checkable shell capacities uniformly on `X`.

The envelope is still unable to close uniformly. If

\[
 (9C)^7>2R,                                               \tag{10.13}
\]

then `x_*=1/(2R)` lies in `X`: for every `1<=d<=2R-2`,
`||d*x_*||>=1/(2R)>(9Cd)^(-7)`. At this admissible test point,

\[
 F_{R-1}(x_*)=\frac1{R\sin^2(\pi/(2R))}
 >\frac{4R}{\pi^2}>\frac R4=T.                         \tag{10.14}
\]

Here `sin y<y` for `y>0` and `pi^2<16` were used. Since the exact square at
`x_*` is bounded above by the positive-shell expression in (10.11),

\[
 \boxed{U_{\rm pack}^{\sharp}>T^2,\qquad
 F_{R-1}(x_*)-T>
 \frac{R(16-\pi^2)}{4\pi^2}>0.}                        \tag{10.15}
\]

Thus even the strongest packing envelope allowed by all pinned-theorem
constraints arising inside the transported Fejer support is provably
non-closing throughout the unconstrained regime (10.13). No constraint at a
difference outside `1<=d<=2R-2` is relevant to this envelope or asserted for
its test point.

## 11. Fejer inequality and the exact closing condition

For this one-point stratum the geometric-series formula is stronger than the
pair-packing relaxation:

\[
 E=\frac1R\left|\sum_{v=0}^{R-1}e(9Cv\pi)\right|^2
 =\frac{\sin^2(\pi R(9C\pi))}
 {R\sin^2(\pi(9C\pi))}.                                 \tag{11.1}
\]

The elementary inequality `|sin(pi*x)|>=2||x||` and (3.3) at `q=9C` give

\[
 \boxed{E<\frac{(9C)^{14}}{4R},\qquad
 E^2<\frac{(9C)^{28}}{16R^2}.}                          \tag{11.2}
\]

Substitute `R=20U` and `T=R/4=5U`. The direct bound (11.2) would refute the
strict T38 spike exactly under the sufficient comparison

\[
 \frac{(9C)^{14}}{4R}\leq\frac R4
 \quad\Longleftrightarrow\quad
 \boxed{(9C)^7\leq20U.}                                \tag{11.3}
\]

Neither T26 nor T38 supplies (11.3): `C` is the product of all preceding
base-ten factors, while `U` is only the next factor. The available statements
give lower bounds on both and no seventh-power domination of `C` by `U`.

## 12. Same-normalization final comparison

Combining every justified upper bound in the same squared normalization gives

\[
 \boxed{
 E^2\leq B_{46}:=\min\left\{
 R^2,
 U_{\rm pack}^{\sharp},
 U_{\rm pt},
 \frac{(9C)^{28}}{16R^2}
 \right\},
 \qquad T^2=\frac{R^2}{16}=25U^2.}                      \tag{12.1}
\]

The packing deficit in the regime `(9C)^7>2R` is explicit in (10.15). The
termwise irrationality bound is even closer to the trivial pair mass. Since
`C>=9`, one has `9C>=81` and
`2*pi/(9Cd)^7<1/4`; the inequality `cos y>=1-y^2/2` gives

\[
 U_{\rm pt}>\frac{31}{32}R^2,
 \qquad U_{\rm pt}-T^2>\frac{29}{32}R^2.                \tag{12.2}
\]

There are now three exact regimes. If `(9C)^7<=R=20U`, (11.2) closes this
local stratum. If `(9C)^7>2R`, then (10.15), (12.2), and (11.2) show that every
entry in (12.1) is numerically above `T^2`, so the strongest displayed bound
does not close. The intermediate window

\[
 R<(9C)^7\leq2R                                         \tag{12.3}
\]

is not decided by these inequalities. T26 and T38 force none of the three
regimes because they give no seventh-power comparison between the accumulated
multiplier `C` and the next factor `U`.

The exact arithmetic deficit is therefore seven powers of the accumulated
multiplier: irrationality supplies distance `(9C)^(-7)`, whereas T38 supplies
only `delta=(20U)^(-1)`. Closing by this route requires the unproved factor
domination `(9C)^7<=20U`; even excluding the explicit non-closing regime would
require `(9C)^7<=40U`. This conclusion is local and sketch-level. It makes
no unconditional FSFS, compatibility, fixed-`pi` cancellation, C1, or
canonical-A1 claim.

## 13. Reproduction

From a directory containing only the delivered artifacts, run

```bash
python3 verify_note.py
```

The verifier checks all five pinned dependency hashes, source and theorem
locator anchors, the complete weighted multiplicity formulas for
`2<=R<=200`, the difference multiplicities, the 10-adic partition, and the
required terminal/non-claim markers. These finite checks audit transcription
and algebra; they are not evidence for a universal fixed-`pi` claim.

INSUFFICIENT
