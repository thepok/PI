# T103: positive-entropy Toeplitz tower audit

Claim labels: the two-source corpus and the statements attributed to it are
`literature-checked`.  The collision translations and elementary deductions
below are a `proof sketch`.  The replay is an `experiment` which checks
transcription on finite ranges; it is not evidence for a universal claim.

TERMINAL_VERDICT: close

## 1. Provenance, scope, and immutable statement

Agenda item: `T103`, serving `G28`.

Canonical source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
Original source URL: none; this is a local formulation recorded on 2026-07-22.
The byte-exact delivered copy is `canonical_statement.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question concerns the fixed decimal orbit of `pi`, strict circle
distance, ordered pairs including the diagonal, and the quantifiers

```text
for every integer A >= 1, there exists n0 >= 1 such that
for every integer n >= n0, there exists N >= 1 such that
A*n*Q_pi(n,N) <= N^2.
```

T103 changes the point, alphabet, predicate, and prefix sequence.  It is an
A13/A14 symbolic sibling audit.  It makes no assertion about `pi`, C1, C2,
canonical A1, normality, decimal factor complexity, or digit occurrence.

### Normalized ambiguities

1. "Explicit point" means a coordinatewise defined sequence, not merely an
   invariant measure, an almost-everywhere orbit, or existence of a point in a
   subshift.
2. "Positive entropy" means positive topological entropy of the orbit closure,
   not positive entropy of some unrelated measure or source sequence.
3. A prefix cutoff restricts block starts only.  A length-`m` block beginning
   at `N-1` may inspect symbols beyond the cutoff.
4. Collision pairs are ordered, the diagonal is included, and overlapping
   occurrences are allowed.
5. A stage period controls only coordinates already filled at that stage.  It
   is not silently promoted to a period of the complete irregular Toeplitz
   point.
6. Block-complexity growth counts distinct words somewhere in the language.
   It does not bound their multiplicities in a declared prefix.
7. The unavailable concurrent item T100 is not treated as a premise or as an
   established comparator.

## 2. Bounded corpus

```text
RETAINED_CANDIDATE_COUNT: 1
RETAINED_PRIMARY_SOURCE_COUNT: 2
candidate cap: 1 <= 3
primary-source cap: 2 <= 8
```

The sole candidate is the power-of-five specialization of the
El Abdalaoui--Kasjan--Lemanczyk irregular Mobius-Toeplitz point.  We denote it
by `z_5`.  It is retained because its coordinates, nested periods, and holes
are explicit and its positive entropy is source-checked.  No finite-rank
candidate is needed because the agenda permits Toeplitz *or* finite-rank
systems, and adding a qualitatively specified construction would weaken the
named-point requirement without changing the collision obstruction.

The retained primary sources are:

| ID | Primary source | Exact role |
|---|---|---|
| S1 | El Abdalaoui, Kasjan, Lemanczyk, *0-1 sequences of the Thue-Morse type and Sarnak's conjecture* | Coordinate construction, stage progressions, pointwise Toeplitz property |
| S2 | Downarowicz, Kasjan, *Odometers and Toeplitz systems revisited in the context of Sarnak's conjecture* | General filling scheme, period-block geometry, positive entropy of S1's example |

`SOURCE_PINS.md` records DOI and URL data, PDF and derivative hashes, and
page/line locators.  `SEARCH_LOG.md` records the bounded search and exclusions.

## 3. The named point and its exact pointwise theorem

Let `a_r=5^r` for integers `r>=1`.  Define subsets `A_n` of the nonnegative
integers recursively.

```text
A_0 = {5k : k>=0}.

For n>0:
  if n belongs to some previously defined A_u, put A_n=A_u;
  otherwise put A_n={n+k*5^(n+1) : k>=0}.
```

Different newly created progressions are disjoint.  Let `iota(n)` be the least
element, called the initial, of `A_n`.  Extend the classical Mobius function by
the source convention `mobius(0)=0`; at positive integers use its usual value.
The named point is

```text
z_5(n) = mobius(iota(n)),        n>=0.                       (3.1)
```

This is S1's construction at its expressly allowed choice `a_r=5^r`: S1
printed pp. 12--13, equation (24), the parenthetical example, and the recursive
definition immediately before Proposition 5; delivered derivative lines
751--787.  It defines each coordinate without choosing a measure or generic
point.

### Pointwise return theorem

For every `n>=0`, every `q>=0`, and `u=iota(n)`, S1's progression property
gives

```text
z_5(n+q*5^(u+1)) = z_5(n).                                 (3.2)
```

Indeed `A_n={u+k*5^(u+1):k>=0}`, so both indices have the same progression and
the same initial.  This is the exact pointwise Toeplitz theorem used here.  Its
quantifiers are pointwise: the period depends on the coordinate through `u`.
S1 says explicitly that property 3 makes `z` a Toeplitz sequence at printed
p. 13, delivered derivative lines 768--787.

For a start `i>=0` and block length `m>=1`, put

```text
r(i,m) = max {iota(i+t) : 0<=t<m},
h(i,m) = 5^(r(i,m)+1).                                      (3.3)
```

Every coordinate period in the block divides `h(i,m)`.  Hence, for every
`q>=0`,

```text
z_5[i+q*h(i,m), i+q*h(i,m)+m) = z_5[i,i+m).                (3.4)
```

Equation (3.4) is an elementary simultaneous use of (3.2), not a uniform
return-time theorem quoted from the source.

## 4. Nested stage towers and exact hole density

For stage `R>=0`, declare the tower height

```text
H_R = 5^(R+1).                                              (4.1)
```

Let `I_R` be the set of initials at most `R`.  The coordinates already filled
by these initials form an `H_R`-periodic set `U_R`.  Within one period, the
progression with initial `u` occupies exactly `H_R/5^(u+1)` residues.  Since
the progressions are disjoint, the exact resolved and hole densities are

```text
rho_R   = |U_R intersect [0,H_R)|/H_R
        = sum_(u in I_R) 5^(-(u+1)),

delta_R = 1-rho_R.                                         (4.2)
```

As `I_R` is a subset of `{0,...,R}`,

```text
rho_R <= sum_(u=0)^R 5^(-(u+1))
       = (1-5^(-(R+1)))/4,

delta_R >= 3/4 + 1/(4*5^(R+1)) > 3/4.                     (4.3)
```

Thus these are nested periodic-hole towers with `H_R | H_(R+1)`, but their
unresolved density does not tend to zero.  This is the normalized mechanism
fingerprint: **periodic-hole tower geometry with a uniformly positive hole
density**, not a globally periodic approximation.

S2 Example 6.3, printed pp. 13--14 and derivative lines 684--769, gives the
same first-available-position filling scheme for a general scale.  S2 Lemma
7.1(1)--(3), printed pp. 14--15 and derivative lines 786--822, separates first
placements from periodic repetitions and computes their densities.  Equations
(4.1)--(4.3) are the exact power-of-five specialization, also directly
checkable from S1's disjoint progressions.

## 5. Positive entropy, with source boundary

Let `I_infinity` be the set of all actual initials.  The periods used by the
successive genuine placements are `5^(u+1)` for `u` in `I_infinity`, so S2's
density parameter specializes to

```text
rho_* = sum_(u in I_infinity) 5^(-(u+1))
      = lim_(R->infinity) rho_R <= sum_(u>=0) 5^(-(u+1))
      = 1/4.                                                (5.1)
```

S2 Section 8, "Entropy of the Example 6.3", printed pp. 18--22 and derivative
lines 948--1157, proves positivity for the S1 example.  The proof compares
length-`n` words in the squarefree indicator `|mobius|`, whose subshift entropy
is `(6/pi^2)*log 2`, with words in `z_5`.  At derivative lines 964--977 it
derives, after errors tend to zero, the lower bound

```text
h_top(orbit-closure(z_5)) >= (6/pi^2-rho_*)*log 2
                           >= (6/pi^2-1/4)*log 2 > 0.        (5.2)
```

The rest of Section 8 constructs suitable translated intervals for every
source word.  Equation (5.2) is a language-complexity statement.  The source
does not say that these occurrences lie with controlled multiplicity in
`[0,H_R)`, nor does it give a maximal-cylinder estimate there.

## 6. Literal collision translation

For any one-sided finite-alphabet point `x`, `m>=1`, and start cutoff `N>=1`,
define

```text
c_x(w;m,N) = #{0<=i<N : x[i,i+m)=w},

E_x(m,N)   = sum_(words w of length m) c_x(w;m,N)^2,

M_x(m,N)   = max_w c_x(w;m,N)/N.                            (6.1)
```

Then, exactly,

```text
E_x(m,N)
 = #{(i,j) in {0,...,N-1}^2 : x[i,i+m)=x[j,j+m)}.          (6.2)
```

Thus the count is ordered, includes all `N` diagonal pairs, allows overlaps,
and restricts starts rather than the inspected containing word.  The elementary
maximal-cylinder bounds are

```text
M_x(m,N)^2 <= E_x(m,N)/N^2 <= M_x(m,N).                    (6.3)
```

The left inequality keeps the largest summand; the right uses
`sum_w c_x(w;m,N)=N`.

### 6.1 Translation of the pointwise return theorem

Fix `i,m`, put `h=h(i,m)`, and assume `i<h`.  At the declared tower-height
prefix `N=q*h`, equation (3.4) supplies the `q` starts

```text
i, i+h, ..., i+(q-1)h.
```

Their length-`m` blocks are equal.  Therefore

```text
E_(z_5)(m,qh) >= q^2.                                      (6.4)
```

Both orientations and the `q` diagonal pairs are already included in `q^2`.
This is an exact lower bound, not the upper bound needed for sparse collisions.

### 6.2 Translation of a whole stage tower

Let `D_R` be the holes in one period and define the good phases

```text
G_(R,m) = {0<=i<H_R : i,i+1,...,i+m-1 avoid D_R modulo H_R}.
```

For each word `w`, let `g_w` count phases in `G_(R,m)` carrying `w`.  At
`N=qH_R`, every good phase repeats `q` times, so

```text
E_(z_5)(m,qH_R) >= q^2 * sum_w g_w^2
                  >= q^2 * |G_(R,m)|,                      (6.5)

|G_(R,m)| >= max(0, H_R-m|D_R|)
            = H_R*max(0,1-m*delta_R).                      (6.6)
```

Equation (6.6) is the union bound for the `m` translates of the hole set.  By
(4.3), it is already vacuous for every `m>=2`.  More importantly, neither
(6.5) nor the sources give an upper bound on the contributions of hole-touching
starts.

### 6.3 Why entropy does not reverse the inequality

Let `p_z(m)` be the total number of length-`m` words in the language.  For any
prefix, Cauchy--Schwarz gives

```text
E_(z_5)(m,N) >= N^2/p_z(m).                                (6.7)
```

Positive topological entropy makes `p_z(m)` exponentially large along the
language, but (6.7) is a lower bound.  It cannot be reversed without frequency
or maximal-cylinder information.  S2 finds specially translated occurrences
to prove language diversity; it supplies no theorem bounding
`M_(z_5)(m,H_R)` or `E_(z_5)(m,H_R)` from above.  The complete source-supported
collision interval is therefore only

```text
H_R <= E_(z_5)(m,H_R) <= H_R^2,                            (6.8)
```

plus the lower-return statements (6.4)--(6.7).  This is the first fatal gap in
the requested quantitative mechanism.

## 7. Exact T14 sibling and comparison

The machine-checked T14 interface is pinned in Section 8.  It concerns the
decimal stream and fixes `mu,eta,d,B,m0,k0,N,nu` outside the triangular
quantifiers

```text
for every k>=k0, for every m with m0<=m<=k:
  d*m-B <= splitting-level-count(m,N(k),mu,eta).            (7.1)
```

Its parent is split when two distinct successors each carry at least an `eta`
fraction of the parent count, and split parents must carry at least a `mu`
fraction of collision energy.  T14 uses `0<eta<=1/10`, one strictly increasing
positive cutoff sequence, and one weak limit of its empirical measures.

The literal ternary sibling for `z_5` replaces decimal words by words over
`{-1,0,1}`.  Put `c(w)=c_(z_5)(w;m,N)` and
`c(wa)=c_(z_5)(wa;m+1,N)`.  A parent `w` is `eta`-split if two distinct
symbols `a,b` satisfy

```text
eta*c(w) <= c(wa),       eta*c(w) <= c(wb).                 (7.2)
```

Define the split energy by summing `c(w)^2` over such parents.  A level is
`(mu,eta)`-splitting when

```text
mu*E_(z_5)(m,N) <= split-energy_(z_5)(m,N,eta).             (7.3)
```

Let `X_5` be the compact one-sided orbit closure of `z_5` in
`{-1,0,1}^N`, let `sigma` be its left shift, and for a cutoff sequence define

```text
nu_k = (1/N(k))*sum_(j=0)^(N(k)-1) delta_(sigma^j z_5).
```

The corresponding coherent sibling asks for fixed

```text
0<mu<1, 0<eta<=1/3, d>0, B>=0, m0,k0,
a strictly increasing N(k)>=1, and nu in Prob(X_5),
```

such that `nu_k` converges weakly to `nu` and (7.1) holds with
(7.2)--(7.3) for every entry of the same triangle.
Because `X_5` is compact metrizable, its probability measures are weakly
sequentially compact.  Passing from the strictly increasing heights `H_R` to a
subsequence therefore supplies this weak-limit clause automatically.  It has
no quantitative collision or successor content.
The conservative `1/3` replaces T14's decimal `1/10`; allowing the logically
largest `eta<=1/2` would not repair any missing source estimate.

For every finite-alphabet point and the same start cutoff,

```text
E_x(m,N)-E_x(m+1,N)
 = 2*sum_w sum_(a<b) c_x(wa;m+1,N)c_x(wb;m+1,N).           (7.4)
```

For a split parent, all child counts sum to `c(w)` and two are at least
`eta*c(w)`.  When `eta<=1/2`, concentrating all remaining mass as much as
possible gives child square-sum at most

```text
((1-eta)^2+eta^2)c(w)^2 <= (1-eta)c(w)^2.
```

Nonsplit parents never increase energy under refinement.  Thus (7.3) gives the
exact T9/T14 local decrement

```text
E_(z_5)(m+1,N) <= (1-mu*eta)E_(z_5)(m,N).                  (7.5)
```

This matches the machine-checked decimal theorem
`quantitativeSplittingLevel_energy_decrement` in T9 lines 210--217.  The
identity (7.4) alone also gives the weaker decrement `2*mu*eta^2`, but (7.5)
records the exact accepted-interface constant.

The source comparison is now clause-complete:

| T14 sibling clause | What S1/S2 give for `z_5` | Result |
|---|---|---|
| Named point | Coordinate formula (3.1) | supplied |
| Nested heights | `H_R=5^(R+1)` and divisibility | supplied |
| Pointwise returns | (3.2)--(3.4), period depending on the coordinate/block | supplied |
| Controlled holes | exact (4.2), but `delta_R>3/4` | opposite of shrinking-hole control |
| Ordered diagonal collision count | exact translation (6.1)--(6.2) | supplied by elementary identity |
| Collision upper bound at one height sequence | only (6.8) and lower bounds | absent |
| Fixed `mu,eta` splitting levels | no successor-frequency theorem | absent |
| Fixed positive density `d` and defect `B` | no adjacent energy decrement such as (7.5) | absent |
| Every `m<=k` at the same `N(k)` | entropy proof chooses word-dependent translated intervals | absent |
| One empirical weak limit on that sequence | available after a subsequence of `H_R` by compactness of `Prob(X_5)` | supplied, but nonquantitative |

No numerical `mu,eta,d,B` can honestly be extracted.  The pointwise periods
translate into collision lower bounds, while T14 coherent splitting requires
repeated upper energy decrement with all constants fixed outside the triangle.

## 8. Non-duplication map

Local hashes below pin the exact accepted-library or sketch-level reports used
for comparison.  A `proof sketch` note is never used as a discharged premise.

| Prior family | Verification status and pin | Exact difference from T103 |
|---|---|---|
| T14 | `machine-checked`; `CoherentSuccessorSplitting.lean`, SHA-256 `bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833`, lines 26--55 and 409--590; T9 `SuccessorSplitting.lean`, SHA-256 `1ee132366d7bd7f3685e37dd4258f2d28c3c386badce71fb6f3bbd845156e354`, lines 185--217 | Abstract fixed-parameter decimal splitting characterization and exact decrement `1-mu*eta`; no periodic skeleton, named model point, or hole geometry. T103 tests whether one source-defined tower supplies its sibling hypotheses and finds that it does not. |
| T39 | `literature-checked`; `REPORT.md`, SHA-256 `ff5ae4e484dfa42957064ab63302729162e5fcc164c4842bbf96c9fbaac93b5d`, Sections 1--5 | Audits compactness pullback, anchored roots, and conditional quasi-Bernoulli comparison. It does not count blocks in an intrinsic periodic-hole tower. |
| T37/T49 | `machine-checked`; SHA-256 `aa0979b629131c6e30c2d8a8dc8c70499ff03d98cd35b2f49841f7669585116c` and `61082f21330c21c22874e31b77af00f365c2995cdcd3909e5399ce89ed28cd93` | Hand-staged decimal stream exhaustively repeats seeds. T49 has fixed `(mu,eta,d,B)=(1/2,1/20,1,0)` at common checkpoints. `z_5` instead has intrinsic arithmetic progressions, persistent holes, and no splitting constants. |
| T88 | `proof sketch`; SHA-256 `ca481e2d235955cbb137dc752a846a6de510cde1416cd0a2af308bb5a382b066`, Sections 3--7 | Selects a Bernoulli-generic point and an ineffective Fourier diagonal with a persistent ray. It has no named explicit point, exact-word tower count, or pointwise periodic return. |
| T90 | source corpus `literature-checked`, transfers `proof sketch`; SHA-256 `730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0`, Sections 3--7 | Uses discrepancy of explicit expanding-map points to upper-bound metric near returns. T103 uses exact symbolic equality and obtains only lower repetition from periodic holes. |
| T91/T94/T97/T101 | `proof sketch` symbolic notes; report hashes `a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e`, `f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10`, `fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e`, `ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e` | Substitution alignment and automatic paperfolding decimation. T101's note argues finite-state paperfolding splitting is uniformly bounded. None uses a positive-entropy irregular Toeplitz point or persistent periodic holes. |
| T95/T98 | `proof sketch`; hashes `08baad91851c1d25ceaa82f86cbe8b728ca2c063f31f01f83c5fa96aea45d8cb` and `b6b8d30499543fadf5be200b85afe3929dcba5b7a7d96061476965060c589f57` | Universal short-versus-remote exact-word charging at `L=b^(floor(n/2))`, then a conditional three-cylinder transport. There is no named dynamical point, tower, hole density, or nested height sequence. |
| T100 | no artifact was present at the audit cutoff `2026-08-09T23:12:30Z` under the T103 knowledge library, workspace `library/t100`, or a T100 workflow record | No mathematical claim is inherited from an unavailable concurrent item. This is an explicit library gap, not evidence of non-overlap. |
| Stoneham family | T90's source-pinned Stoneham/Larcher--Stockinger case and T99 `proof sketch`, T99 report SHA-256 `9778fd0fdc3151b0e3f8888afdb1d1049347e926d266f2981e7daa3bc44af2b4` | Arithmetic rational-period residues create metric close pairs and non-Poissonian pair correlation along denominator scales. They do not form an exact-word successor tree or T14 triangle. |

This table is a mechanism comparison, not a claim that the literature search is
globally exhaustive.

## 9. Explicit transfer hypothesis

The following is a `conjecture` interface, not an established property.

**HT-pi-tower.**  Let `Digits={0,...,9}`.  The decimal digit shift of `pi`
admits integers `H_k | H_(k+1)` and `N_k=q_k H_k`, phase-hole sets
`D_k subset Z/H_k Z` of density `delta_k`, fully labelled model words
`v_k:Z/H_k Z -> Digits`, and errors `epsilon_k`, with the following explicit
coherence.  If

```text
red_(k+1,k): Z/H_(k+1)Z -> Z/H_k Z
```

is reduction, then

```text
D_(k+1) subset red_(k+1,k)^(-1)(D_k),
v_(k+1)(r)=v_k(red_(k+1,k)(r))
whenever red_(k+1,k)(r) is not in D_k.                      (9.1)
```

Thus previously resolved labels persist and later stages may fill old holes.
The full labels on holes are arbitrary bookkeeping labels, so every model
block and frequency vector below is defined on the common decimal alphabet.
The quantitative conditions are

```text
H_k -> infinity, N_k -> infinity,
k*delta_k -> 0, k*epsilon_k -> 0.                           (9.2)
```

Extend `v_k` periodically to a complete decimal stream.  Simultaneously for
every `1<=m<=k`, at most

```text
beta_(k,m) N_k,     beta_(k,m)=(m+1)*delta_k+epsilon_k,      (9.3)
```

of the first `N_k` starts either touch a tower hole in their first `m+1`
phases or have an actual decimal length-`m+1` block different from the
periodic `v_k` block at that start.  The comparison is now between two fully
defined streams over `Digits`; it is startwise, includes successors, and uses
one `N_k` for the entire row `m<=k`.  It is not only weak convergence of
invariant measures or almost-everywhere agreement.

If `f_pi` and `f_model` are the normalized length-`m` block frequency vectors,
(9.3) implies the explicit pointwise discrepancy bounds

```text
sum_w |f_pi(w)-f_model(w)| <= 2*beta_(k,m),

|E_pi(m,N_k)/N_k^2-E_model(m,N_k)/N_k^2|
  <= 4*beta_(k,m).                                         (9.4)
```

The first inequality charges one removed and one inserted label per mismatched
start.  The second uses
`|sum f^2-sum g^2| <= 2 sum|f-g|`.  Thus a quantitative model collision bound
would transfer with a displayed additive error.  To reach the T14 sibling,
the model would additionally need fixed-margin successor inequalities at a
positive density of levels so that the same perturbation cannot erase the two
children.  The retained sources supply neither that model premise nor
HT-pi-tower.

## 10. Smallest cheap discriminator

The smallest test is **tower-hole density**, before computing any collision or
Fourier statistic.  HT-pi-tower requires `k*delta_k -> 0` to control every
`m<=k` in (9.3).  To instantiate its model words from `z_5`, fix any injection
from `{-1,0,1}` into `Digits`, use the coded `z_5` labels on resolved phases,
and fill hole labels arbitrarily.  For this sole retained model, the exact
source-derived formula (4.3) gives

```text
delta_R > 3/4 for every R.                                 (10.1)
```

Hence `z_5` fails the transfer geometry at the first scalar check.  Even if
one ignores (10.1), the sources provide no maximal-cylinder upper bound, and
(6.3) shows why such a bound would be the next necessary statistic.

## 11. Source-pinned negative map

The one candidate and two sources pass the named-point, positive-entropy,
pointwise-period, nested-height, and exact-hole tests.  Their theorem content
then stops in two precise places:

1. pointwise and stage periodicity yield the ordered, diagonal-inclusive lower
   collision bounds (6.4)--(6.7), not an upper bound at the declared prefixes;
2. the entropy proof controls language cardinality on word-dependent translated
   intervals, not maximal cylinder mass, adjacent energy decrement, or fixed
   `mu,eta,d,B` on one triangular prefix sequence.

The exact hole bound (10.1) also rejects the stated transfer hypothesis before
any fixed-number test.  The periodic-hole fingerprint is therefore exhausted
by this bounded corpus as a quantitative T14-sibling mechanism.  This final
classification concerns only the audited model route and has no consequence
for the canonical fixed-number question.

## 12. Replay and review boundary

From a directory containing only the delivered artifacts, run

```text
python3 verify_t103.py
sha256sum -c SHA256SUMS
```

The verifier checks all delivered source hashes, authenticated source markers,
the corpus caps, the unique terminal classification, finite instances of the
progression disjointness, hole-density identity, pointwise block periods,
ordered collision identity, and successor-energy identity.  These checks are
an `experiment`; Sections 3--10 contain the universal `proof sketch`.

Independent review has not occurred.  No novelty claim is made.
