# Finite-cylinder horizon-bootstrap separator

Status: `proof sketch`

Date: 2026-08-27 UTC

## Statement under audit

Let `D=10015` and let `P_D` be the T173 decimal prefix, so

\[
 P_D10^{-D}<\pi<(P_D+1)10^{-D}.
\]

Define the Liouville decimal

\[
 \lambda=\sum_{j\ge1}10^{-j!},\qquad
 \xi=P_D10^{-D}+10^{-D}\lambda.
\]

Then `xi` is transcendental, lies in the same strict T173 cylinder as pi,
and has only digits zero and one after position `D`.  The audited Pro argument
claims the following simultaneous separation:

1. the finite root inequality survives,
   `Re Z^xi_(1000,334)(10000) > 47539/2500`;
2. the generic T172 algebra therefore produces a positive fixed-horizon
   Bellman descendant at every scale;
3. for every `k>D` and every `A<10^k` with `A == 334 (mod 1000)`, the target
   word is absent from the entire decimal expansion of `xi`, and the generic
   T156 contrapositive gives

   \[
   \Re Z^\xi_{10^k,A}(10^k)<-861/1000.
   \]

Thus the finite cylinder, one finite signed root input, and all orbit-generic
coefficient identities cannot force natural-horizon signed control, even for
the coherent descendant class.

## Why the root sign is stable

For the generic decimal orbit `x_n^eta={10^n eta}`, the primitive score obeys
the Lipschitz estimate

\[
 |Z^\xi_{q,A}(N)-Z^\eta_{q,A}(N)|
 \le {2\pi\over9}(10^N-1)|\xi-\eta|
       \sum_u u|p_{q,A}(u)|. \tag{1}
\]

At `q=1000`, positivity of the boundary coefficients and the total positive
mass identity give the coarse bound

\[
 \sum_u u|p_{1000,334}(u)|<5000. \tag{2}
\]

Since `|xi-pi|<10^-10015` and `N=10000`, (1)--(2) make the score perturbation
less than `10^-11`, far below the directed root margin `>2.36*10^-5`.
This is the essential quantitative reason the countermodel can share the
actual-pi signed seed.

## Why natural horizons fail

Every left-descendant label remains congruent to `334 mod 1000`, so its padded
word ends in `334`.  A word of length `k>D` starting in the fractional
expansion must end after the certified prefix.  It therefore cannot occur in
`xi`, whose tail uses only digits zero and one.

The boundary kernel is strictly negative outside the target cylinder.  The
T147/T156 endpoint and scalar estimates convert absence through the natural
horizon into the strict score bound below `-861/1000` for pi.  Independent
audit found that this chain is not merely syntactically specialized:
T147 imports T146's actual-pi phase dichotomy, ultimately using
`nearestIntegerDistance (9*pi) > 13/50`.  Therefore a generic T156 cannot be
invoked without an explicit endpoint-separation premise.

For the concrete `xi` the gap is repairable with the same constants:
the shared cylinder already gives `3.14 < xi < 3.15`, hence
`28.26 < 9*xi < 28.35`, so the nearest integer is 28 and the distance is
strictly greater than `13/50`.  A later independent proof audit confirmed
that T146's seed dependence is exactly this torus-distance premise and that
the remaining T147 Abel, layer-mass and terminal estimates are
seed-independent.  The parameterized T139--T156 replay is therefore a
complete `proof sketch`, but not a machine-checked generic declaration.

## Trust boundary and required audit

The construction, Liouville proof, decimal avoidance, and Lipschitz estimate
are elementary.  Before upgrading this result to `machine-checked`, Lean must
expose generic orbit versions of the T172/T176/T178 transport; parameterize
T146--T156 under the endpoint-separation premise just identified; prove that
premise for `xi`; and check the weighted coefficient estimate (2) against the
literal T139 coefficients.  Canonical decimal-expansion uniqueness for the
Liouville tail must also be stated.  No claim about pi itself follows from the
countermodel.

The separator is deliberately narrow: it does not exclude an actual-pi
horizon theorem.  It proves that such a theorem must import a premise false
for `xi`, hence genuinely fresh information about the uncertified actual pi
tail.  The most economical remaining quantities are

\[
 \Re\bigl(Z^\pi_{q,A}(q)-Z^\pi_{q,A}(10000)\bigr)
\]

or the corresponding prescribed T179 digit/suffix correlation on the fresh
block.  A tighter defect constant or another finite-cylinder identity cannot
cross this separator.

## Roth-optimal upgrade

The Liouville property of the displayed `lambda` is not essential. Let

```text
tau_10 = sum_(j>=1) t_j * 10^-j
```

be the base-ten Thue--Morse--Mahler number and define

```text
xi_TM = P_D * 10^-D + 10^-D * tau_10.
```

Its tail contains only zeroes and ones, so `xi_TM` lies in the same strict
T173 cylinder. Bugeaud's theorem gives `mu(tau_10)=2`; rational affine
invariance therefore gives `mu(xi_TM)=2`. Classical Mahler transcendence also
makes `xi_TM` transcendental. The exact exponent source is Y. Bugeaud,
*On the rational approximation to the Thue--Morse--Mahler numbers*, Annales
de l'Institut Fourier 61 (2011), DOI `10.5802/aif.2666`, already pinned and
audited in the T16 record.

The coherent-target orientation is important. If

```text
q_r = 1000 * 10^r,
A_(r+1) = A_r + d_r*q_r,
A_0 = 334,
```

then the padded target word is

```text
d_(r-1) ... d_1 d_0 334.
```

It ends in `334`; these are left extensions, not nested prefixes of one real
beginning with `334`. For every sufficiently large `r`, the terminal `334` of
any occurrence would lie beyond decimal position `D`, where `xi_TM` has only
zeroes and ones. Hence one `xi_TM` uniformly avoids every sufficiently deep
target on every coherent left ray. No prescribed-ray diagonalization is
needed.

The finite root score is not identical throughout the cylinder. It remains
positive only by the Lipschitz stability estimate (1)--(2) above. Likewise,
the checked T156 theorem is pi-specific. The natural-horizon conclusion for
`xi_TM` uses the unformalized but independently audited generic T146--T156
chain parameterized by

```text
13/50 < nearestIntegerDistance (9*xi_TM).
```

This premise follows from the shared coarse cylinder
`3.14 < xi_TM < 3.15`, which puts `9*xi_TM` strictly between `28.26` and
`28.35`. The same missed-cylinder contrapositive therefore gives at
`proof sketch` level

```text
Re Z^xi_TM_(q_r,A_r)(q_r) < -861/1000
```

eventually for every coherent ray.

This repaired statement remains a `proof sketch`, not `machine-checked`.
It strengthens the separator by showing that transcendence, non-Liouville
behavior, an effective finite irrationality measure, and even the optimal
irrationality exponent `mu=2` do not bootstrap the finite signed seed.

## Kempner--Mahler literal all-child upgrade

An independently audited `proof sketch` strengthens the separator from a
missed-cylinder score bound to literal failure of T189's R1 condition. Put

```text
K = sum_(r>=0) 10^(-2^r),
xi_J = (floor(10^J*pi)+K)/10^J.
```

The generating function `F(z)=sum_(r>=0) z^(2^r)` satisfies
`F(z)=z+F(z^2)`. The Mahler-number result of
[Bugeaud--Han--Wen--Yao](https://arxiv.org/abs/1503.02797) gives
transcendence and `mu(K)=2`; rational affine invariance gives the same exponent
for `xi_J`. Directly from the gaps between powers of two,

```text
omega(K) = {0} union {10^(-r): r>=1}.
```

Thus `xi_J` has an infinite omega-limit set and an exact scalar Mahler
recurrence while sharing the first `J` decimal places of pi.

Fix `J=10015`. For `q=10^k`, `Q=10q`, `k>=14`, every coherent descendant
label `A == 334 (mod 1000)` and every child `d<10` names a word ending in
`334`; it cannot occur in the post-prefix zero/one tail. Hence every fresh
spatial kernel term is nonpositive. The power-of-two gaps also give the
uniform primitive-endpoint estimate

```text
|Delta E_(k,A,d)| < 10^-6337,
```

with decreasing right side for larger `k`. The exact T128 zero coefficient
satisfies

```text
45*q*alpha_(10q) > pi^2-3.
```

Substitution into the complete T174 spatial identity, without deleting any
character or endpoint channel, yields

```text
D^xi_J_(q,A,d) < -(3/4)*(pi^2-3)*q < 0
```

for every such `A,d`. Therefore at and beyond `q=10^14`, every possible
coherent `334` descendant fails R1 in all ten children. This is not a
counterexample to an actual-pi theorem. It shows that arbitrary finite pi
prefixes, `mu=2`, infinitely many limit points, scalar Mahler recurrence, and
the orbit-generic carrier algebra still cannot supply the required
target-aligned sign. Reopening requires an unbounded exact input special to
the distinguished pi tail and false for these continuations.

## Infinite same-time ladder still does not control the natural prefix

A later independently audited `proof sketch` sharpens the alignment. For any
finite number `D` of fractional digits of pi, insert after that prefix a long
zero gap, a digit `c`, the marker `3345`, and then a zero/one
Kempner--Mahler tail. The marker gives a literal central root at one fixed time
`N`. Recursively replaying the phase-generic content of T193 and T176 at that
same time produces one coherent infinite left-extension ray with

```text
150 < U_(q_0,A_0)(N) < U_(q_1,A_1)(N) < ... .
```

Choose `c != d_0`, where `d_0` is the first selected left-extension digit.
The continuation then contains exactly one post-prefix copy of `334`, but no
sufficiently deep selected descendant: every descendant ends in `d_0 334`,
whereas the unique marker is preceded by `c`. Once `q_r>N`, the distinguished
positive unit lies inside the natural horizon, yet the parameterized
T146--T156 missed-cylinder argument gives

```text
Re P_(q_r,A_r)(q_r) < -861/1000,
S_(q_r,A_r)(0,q_r) < -(861/1000)q_r - 7/3.
```

Consequently the sum of all other natural-prefix unit blocks is less than
`-(861/1000)q_r - 457/3`. The continuation can be transcendental with
irrationality exponent `2`. This isolates the prefix--tail firewall: an entire
fixed-time Bellman ladder is a function of the single suffix `x_N`, while the
natural prefix is not. The constants and decimal construction have been
audited, but the claim remains a `proof sketch` because T193, T176 and
T146--T156 are currently declared only for `piOrbit`; their phase-generic
replays have not been machine checked.

## Prescribed central atoms do not force fresh positivity

An independently audited, normalization-dependent `proof sketch` gives a
finer finite-cylinder separator at the hard node
`q=10000`, `Q=100000`, `A=1334`.  After the pinned first 10015 digits of pi,
concatenate seven-digit blocks

```text
C   = 5133450                 (100 copies),
R_d = d133510                 (834 copies for every d != 5),
R_5 = 5133510                 (5001 copies),
```

and fill the remaining fresh window with eights. Copy forty endpoint digits
from the start of the old window and then attach a `mu=2` Mahler tail. At
every `C` start, child `5` has normalized radius in `[0,1/100)` and boundary
kernel value `>24/5`. At every `R_d` start, child `d` has radius in
`[3/5,61/100)` and kernel value `<-3/25`. Only `C` contains a programmed
digit `4`, so the fresh window has exactly those 100 controlled positive
target hits and at most twenty uncontrolled boundary starts.

The resulting upper kernel sums are

```text
d != 5: 20*5 - 834*(3/25)         = -2/25,
d  = 5: 20*5 + 100*5-5001*(3/25) = -3/25.
```

Together with the copied-endpoint bound and exact stopping identity, these
imply `D_d<0` for all ten children. Thus even one hundred prescribed,
same-child central atoms with a uniform positive kernel margin do not force
R1: a principal annular predecessor packet can overwhelm them.

Rotating only the excess `4167` adverse starts from predecessor digit `5` to
digit `6` leaves the unweighted count vector's zero mode and every DFT
magnitude unchanged, but changes the controlled estimate to
`D_5>15549997.8`. This isolates target-relative predecessor orientation as
the missing datum.

The preservation claim is deliberately limited. The completions share the
pinned prefix, chamber counts, unweighted count-spectrum magnitudes,
endpoint-copy bound, irrationality exponent and eventual orbit tail. They do
**not** have exactly equal old scores, exact central kernel weights, or
kernel-weighted leakage spectra; later digits perturb those quantities. The
abstract cyclic-vector separator preserves such phase-blind data exactly,
but has not been realized as two decimal completions with identical old
score. Reopen only with an actual-pi theorem controlling the weighted
central/annular/old-deficit cross-phase, not central recurrence or
phase-blind annular counts alone.

An independently audited unbounded variant sharpens the same fatal line
(`proof sketch`). One may prescribe a coherent literal digit-`1` ray
beginning at `151334` and construct a transcendental decimal `xi` with
irrationality exponent `mu(xi)=2`, sharing any chosen finite prefix of pi,
such that every sufficiently large natural fresh block contains two exact
central predecessor pairs for the selected child, yet

```text
D_1 < -Q/225.
```

The construction inserts two central packets and `1000*K^2` packets in the
fixed adverse annulus `3/5<=|y|<=5/8` at scale `Q=10^(K+1)`. Sparse
prescription uses only `O((log N)^4)` digits below position `N`; a
Borel--Cantelli argument controls accidental target hits and preserves
`mu=2`. Thus two recurrent correctly oriented atoms, finite irrationality
exponent, transcendence, and arbitrary finite pi-prefix data still do not
force the full fresh sign. This is a replacement-orbit separator, not an
assertion about pi.
