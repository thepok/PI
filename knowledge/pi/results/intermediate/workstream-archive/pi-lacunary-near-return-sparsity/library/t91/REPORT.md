# T91: structured synchronization models with exact collision tests

Search and audit date: 2026-08-09 UTC.

## 1. Scope, labels, and canonical statement

This survey retains exactly three low-description systems:

1. the binary Thue--Morse substitution;
2. the binary period-doubling substitution;
3. the regular paperfolding word.

The source claims below are `literature-checked` as recorded in
`SOURCE_PINS.md`.  The universal collision formulas for the first two systems
are complete elementary `proof sketch` derivations, not machine-checked
theorems.  The bounded replay is an `experiment`; it is not evidence for a
universal statement or for pi.

The vendored canonical statement has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks, for every integer `A >= 1`, for every sufficiently large depth `n`,
for some `N=N(A,n)`, whether

```text
A*n*Q_pi(n,N) <= N^2,
```

where `Q_pi` counts ordered, diagonal-inclusive pairs among the first `N`
points of the fixed circle orbit `10^j*pi`, using strict radius `10^(-n)`.
None of the three binary sibling systems changes those quantifiers or proves a
property of pi.  In particular, exact factor equality is only ambiguity A10,
and substitution or automatic siblings are A13/A14.

## 2. Common exact statistic

For a finite word `W` of length `P`, a block length `L | P`, and
`Q=P/L`, sample only aligned starts `0,L,...,(Q-1)L`.  If `c(u)` is the
number of sampled blocks equal to `u`, define

```text
E_al(W,L) = sum_u c(u)^2.
```

This counts ordered, diagonal-inclusive equal-block pairs on the aligned
sample.  It is deliberately named `E_al`: it is not T14's all-first-start
energy at one fixed prefix size.  The distinction is load-bearing.

For comparison with a same-mass tree, one can formally inflate each aligned
start by its cell width and put `C(u)=L*c(u)`.  Then `sum C(u)=P` and
`E_inf=sum C(u)^2=L^2 E_al`.  This inflation is only a diagnostic.  It does
not turn a substitution tiling into pi's overlapping first-start count tree.

## 3. Candidate 1: Thue--Morse

### 3.1 Source-pinned system

Let

```text
mu(0)=01,  mu(1)=10,  t=lim_K mu^K(0).
```

Balkova's paper, pinned as S1, defines this as the `b=m=2` generalized
Thue--Morse fixed point and gives its synchronization and exact factor-frequency
framework.  The calculation below needs only the displayed substitution.

This is not a handcrafted stream: one fixed two-letter morphism generates all
positions.  It is also not a Walsh comparator: no character sum, spectral
norm, or Parseval identity enters the calculation.

### 3.2 Exact aligned collision calculation

Fix integers `K>r>=0`, put `s=K-r`, `L=2^r`, and `Q=2^s`.  Write

```text
mu^s(0)=a_0 ... a_(Q-1).
```

Because `mu^r` is a monoid morphism,

```text
mu^K(0)=mu^r(a_0) ... mu^r(a_(Q-1)).                 (TM1)
```

The two supertiles `mu^r(0)` and `mu^r(1)` are distinct.  For `s>=1`, every
image under `mu` contains one zero and one one, so `mu^s(0)` contains exactly
`Q/2` of each letter.  Consequently the aligned occupancies and energy are

```text
c(mu^r(0))=c(mu^r(1))=Q/2,
E_al=2*(Q/2)^2=Q^2/2.                                (TM2)
```

This is an exact ordered, diagonal-inclusive collision identity for every
`K>r`; it is not inferred from complexity.

After the diagnostic mass inflation, both occupancies are `P/2`, hence

```text
E_inf=P^2/2                                                   (TM3)
```

at every supertile order.  There is no same-mass one-step energy decrement.

### 3.3 Bounded falsifier

At `K=4,r=2`, `mu^4(0)` has four aligned length-four blocks:

```text
0110, 1001, 1001, 0110;  counts=(2,2);  E_al=8;  Q=4.
```

Moving from `r=1` to `r=2` halves the natural aligned sample from eight starts
to four.  Inflating both rows back to `P=16` gives energy `128=P^2/2` in both
rows.  Thus the natural supertile hierarchy falsifies any proposed direct
substitution into T64's strict same-prefix decrement
`E_(ell+1)<(1/2)E_ell`.

### 3.4 Pi-specific transfer hypothesis and kill condition

**TM-transfer-to-T14.**  A proposed implementation must provide a fixed
increasing pi prefix sequence `N_k` and, on a positive-density triangle of
ordinary decimal depths `ell<m<=k`, a mass-preserving map from all `N_k`
overlapping pi starts at depths `ell,ell+1` to a recognizable supertile
hierarchy.  At fixed `eta`, it must put at least an `eta` fraction of each
selected parent's count on two distinct children; at fixed `mu`, the selected
parents must carry at least a `mu` fraction of row collision energy.  The
number of such levels must be at least `d*m-B`, with all `mu,eta,d,B` fixed.
This is the literal shape needed for T14's
`QuantitativeSplittingLevel ell (N k) mu eta`.

**Bounded rejection gate.**  Before using pi, any claimed supertile
implementation must exhibit the same total start mass in its parent and child
rows and show that its energy change is not caused by deleting starts.  Test
that claim on `mu^4(0)` at `r=1,2`.  The natural aligned implementation has
total masses `8,4`, not one common mass; after the only uniform cell-width
inflation to mass 16, both energies are 128, so it has no decrement.  This test
therefore falsifies a claimed implementation whenever its transfer map is the
natural aligned decomposition or any copy of it that predicts a decrement
solely from `Q -> Q/2`.  A different implementation can survive only by
supplying the missing all-start map explicitly.

**Verdict: close.**

The exact synchronization is real, but its collision improvement is entirely
tied to moving aligned samples and cannot instantiate T14 or T64 on one fixed
prefix row.

## 4. Candidate 2: period-doubling

### 4.1 Source-pinned system

Let

```text
sigma(0)=01,  sigma(1)=00,  w=lim_K sigma^K(0).
```

Polakova's paper, pinned as S2, gives this fixed point and equations
(2.1)--(2.2) for its substitution and supertiles.  Unlike Thue--Morse, this
substitution is not letter-balanced; it tests whether a primitive biased
substitution repairs the transfer failure.

It is generated by one fixed morphism, not staged by hand.  The calculation is
literal block equality, not Rudin--Shapiro/Walsh cancellation.

### 4.2 Exact aligned collision calculation

Let `Z_s,O_s` count zeroes and ones in `sigma^s(0)`.  From the two images,

```text
Z_(s+1)=Z_s+2*O_s,  O_(s+1)=Z_s,  (Z_0,O_0)=(1,0).  (PD1)
```

Induction gives, with `e_s=(-1)^s`,

```text
Z_s=(2^(s+1)+e_s)/3,
O_s=(2^s-e_s)/3.                                      (PD2)
```

The divisions are integral because `2^s` is congruent to `e_s` modulo three.
The two supertiles remain distinct: the equal-length codewords `01` and `00`
can be uniquely parsed, so the morphism is injective on finite words.

For `K>r>=0`, put `s=K-r`, `L=2^r`, and `Q=2^s`.  The same monoid
decomposition as (TM1) gives exactly two aligned block types with occupancies
`Z_s,O_s`.  Therefore

```text
E_al=Z_s^2+O_s^2
    =(5*4^s + 2*2^s*e_s + 2)/9.                       (PD3)
```

In particular `E_al/Q^2 -> 5/9`.  This is an exact collision formula, not a
factor-complexity estimate.

### 4.3 Bounded falsifier

At `K=5,r=2`, the eight aligned length-four blocks are the two supertiles
`0100` and `0101` with counts `(5,3)`, so `E_al=34`.  At `r=3`, the counts are
`(3,1)` and `E_al=10`.  Inflating to the common mass `P=32` gives

```text
r=2: E_inf=4^2*34=544,
r=3: E_inf=8^2*10=640.
```

The same-mass energy increases.  Thus bias does not repair the direct T64
decrement; the apparent uninflated decrease again comes from discarding half
the starts.

### 4.4 Pi-specific transfer hypothesis and kill condition

**PD-transfer-to-T64.**  A proposed implementation must give a pi-specific
finite-state representation that evaluates T64's actual half-open decimal
cylinders at one fixed cutoff `P=N_k`, and it must prove both T64's displayed
active-boundary bound and collected circle-Fourier remainder bound.  Its state
map must preserve all `P` overlapping starts in both adjacent rows.

**Bounded rejection gate.**  Test the claimed row map on `sigma^5(0)` at
`r=2,3`, requiring the common mass `P=32`.  The natural aligned map has masses
`8,4`; uniform mass restoration gives energies `544,640`.  Since `640` is not
less than `544/2`, this exactly falsifies any claimed T64 implementation whose
finite-state row map is this aligned map (or one preserving these fibers) and
whose strict decrement was inferred from uninflated energies `34 -> 10`.
Other implementations must expose a genuinely new all-start representation,
boundary estimate, and circle-Fourier estimate to pass the gate.

**Verdict: close.**

The biased incidence matrix changes the exact collision constant but not the
sampling mismatch.  It adds no viable T64 premise.

## 5. Candidate 3: regular paperfolding

### 5.1 Source-pinned system and theorem

Use the one-based regular paperfolding word `p`: if

```text
n=2^a(2*j+1),  then p_n = j mod 2.                    (PF1)
```

This is one valuation/odd-part rule, not an arbitrary stream.  Allouche and
Bousquet-Melou, pinned as S3, define canonical position sets by

```text
P_1={1,2,3,6},
P_(2k)  =(2*P_k-1) union (2*P_k),
P_(2k+1)=(2*P_k-1) union (2*P_(k+1)).                 (PF2)
```

Their Theorem 2 states that for every `k>=7`, `|P_k|=4k` and the map sending
`q in P_k` to the length-`k` factor beginning at `q` is a bijection onto all
length-`k` factors.  This is stronger than a bare complexity count: it gives an
explicit synchronization transversal and says its block-collision relation is
exactly equality of positions.

Thus the ordered, diagonal-inclusive collision energy on the canonical
transversal is exactly

```text
E_can(k)=4k.                                           (PF3)
```

No Walsh character occurs in (PF1)--(PF3).  The valuation rule is a carry-like
mechanism, but it supplies literal factor representatives rather than T67's
digitwise Parseval identity.

### 5.2 Bounded exact example and falsifier

The recursion gives

```text
P_7={1,...,12,14,15,16,18,19,20,21,22,23,24,
     42,43,44,46,47,48}.
```

The 28 canonical length-seven factors are pairwise distinct.  Direct use of
(PF1) also gives the noncanonical collisions

```text
B_7(13)=B_7(5) =0110001,
B_7(17)=B_7(1) =0010011,
B_7(45)=B_7(21)=0111001.
```

Among all starts `1,...,48` there are still 28 factor types, but the actual
ordered, diagonal-inclusive collision energy is `98`, not the canonical
energy `28`.  This exactly falsifies the tempting replacement of full-prefix
collision energy by collision energy on a canonical transversal.

### 5.3 Pi-specific transfer hypothesis and kill condition

**PF-transfer-to-T83.**  At T83's sample length `L_n=10^(floor(n/2))`, a
proposed implementation must provide a fixed-pi carry transducer that maps
every strict circle near-return in the residual long sector either to an exact
equal decimal block or to one of uniformly bounded extra carry states.  It
must give complete fiber multiplicities, not merely representatives, and prove
T83's all-rates `ResidualLongSectorSubexponential` bound.  Together with the
effective-irrationality premise, this is the named near-return route.

**Bounded rejection gate.**  Any claimed implementation based only on the
canonical representative map must reproduce full first-start collision energy
on the source model.  At `k=7`, the canonical map gives `E_can=28`, while all
starts `1,...,48` give `E_first48=98`.  The three displayed fibers witness the
loss.  This test exactly falsifies every representative-only transfer, or any
claimed multiplicity-one transfer.  A surviving carry transducer must output
the full multiplicities and metric carry states.

**Verdict: hold as model.**

The canonical-position theorem is a clean, low-description synchronization
mechanism absent from the current pi input.  It remains useful as a model for
what a carry-state collision atlas would look like, but supplies no decay or
pi transfer.

## 6. Clause-by-clause accepted-interface comparison

| interface clause | Thue--Morse | period-doubling | paperfolding |
|---|---|---|---|
| **T14.1:** fixed `0<mu<1`, `0<eta<=1/10`, `d>0`, `B>=0` | No successor predicate or constants; (TM2) is collision-only. | No successor predicate or constants; (PD3) is collision-only. | No weighted successor predicate. |
| **T14.2:** one `StrictMono N`, positive cutoffs, and one weak limit | Natural aligned cutoff changes with order; no empirical circle measure. | Same; no empirical circle measure. | `P_k` changes with factor length and is not an empirical prefix sequence. |
| **T14.3:** every `k>=k0` and every `m0<=m<=k` use the same cutoff `N(k)` | Fails exactly: aligned mass halves at each supertile order. | Fails exactly: aligned mass halves at each order. | Theorem 2 is levelwise; it has no common triangular row. |
| **T14.4:** at least `d*m-B` levels split by collision-energy mass | No such count; common-mass energy is constant. | No such count; bounded common-mass energy increases. | Canonical uniqueness is not splitting. |
| **T37.1:** one stream built from exhaustive repeated-seed stages | One fixed two-state morphism, so genuinely different from the handcrafted stages. | One fixed primitive morphism, also different. | One valuation/odd-part rule, also different. |
| **T37.2:** exact overlapping first-start conservation | Aligned starts omit most first starts; the natural row mass changes. | Same. | Canonical positions are a transversal, not a conserved all-start count tree. |
| **T37.3:** moving roots/checkpoints with normalized full leakage tending to zero | No leakage theorem; supertile alignment is moving-scale only. | No leakage theorem. | No leakage statistic or limit. |
| **T37.4:** no stable original-coordinate half-dominant branch | Not studied or implied. | Not studied or implied. | Not studied or implied. |
| **T49.1:** actual artificial-tail empirical measures converge to Haar | No circle empirical theorem is used. | None. | None. |
| **T49.2:** fixed witnesses `(mu,eta,d,B)=(1/2,1/20,1,0)` | No analogue. | No analogue. | No analogue. |
| **T49.3:** every `ell<m<=k` is a splitting level at the same sampled checkpoint | Downsampled aligned collision identity only. | Downsampled aligned collision identity only. | One representative per factor, not child splitting. |
| **T49.4:** coherent splitting coexists with no original-coordinate branch | Neither conjunct is proved. | Neither conjunct is proved. | Neither conjunct is proved. |
| **T64.1:** actual `piOrbit`, literal half-open parent/successor cylinders, same `P=N(k)` | Binary aligned supertiles, not pi cylinders. | Same. | Binary factors at canonical positions, not pi cylinders. |
| **T64.2:** parent cutoff `40q^3`, successor cutoff `8000q^3`, and both active-boundary budgets | No boundary statistic. | No boundary statistic. | No boundary statistic. |
| **T64.3:** collected circle-Fourier remainder at most `P^2/(10q)` | No circle coefficient. | Incidence eigenvalues are not the required circle remainder. | Carry-like valuation states do not evaluate the remainder. |
| **T64.4:** premises force `E_(ell+1)<E_ell/2` and the literal T14 row | Common-mass energy is equal in the bounded gate. | Common-mass energy increases in the bounded gate. | Canonical versus full energy already differs. |
| **T67.1:** actual pi Walsh words equal actual pi cylinder codes | Literal model words only; no pi identity. | Same. | Same. |
| **T67.2:** nontrivial Walsh Parseval sum equals centered cylinder energy | No Walsh transform is used, distinguishing this from a Walsh comparator. | No Walsh transform is used. | No Walsh transform is used. |
| **T67.3:** abstract top-shell arrays are explicitly not orbit witnesses | The supertile formula is a realizable model identity but not a pi witness. | Same. | The canonical atlas is realizable but not a pi witness. |
| **T83.1:** C7 is strict circle near return `Q_pi`, not exact equality | Exact binary equality only. | Exact binary equality only. | Exact binary equality only. |
| **T83.2:** prescribed sparse scale `L_n=10^(floor(n/2))` | Dyadic model sizes, no transfer to `L_n`. | Dyadic model sizes, no transfer. | Factor length and canonical positions, no `L_n` theorem. |
| **T83.3:** diagonal plus unconditional short-sector budget | Not decomposed. | Not decomposed. | Not decomposed. |
| **T83.4:** exact-long all-rates bound reaches exact collision C2 | No all-rates long-sector estimate. | None. | Canonical representatives omit multiplicities, as the `k=7` gate shows. |
| **T83.5:** near-return route additionally needs effective irrationality and residual-long all-rates decay | Neither premise. | Neither premise. | Both are explicit missing clauses in PF-transfer-to-T83. |
| **Memory M1:** moving windows or one checkpoint cannot replace one absolute-root increasing prefix sequence | Violated by changing aligned samples. | Violated by changing aligned samples. | Levelwise `P_k` does not supply the sequence. |
| **Memory M2:** collision classification/frequency injectivity does not evaluate the prescribed pi coefficient | Exact classification only. | Exact incidence only. | Exact canonicalization only. |
| **Memory M3:** Walsh regrouping is not circle decay because of carries | No regrouping is renamed as decay. | No incidence identity is renamed as decay. | Carry-like model states are explicitly not a circle estimate. |
| **Memory M4:** exact phase regrouping is not cancellation | No phase claim. | No phase claim. | No phase claim. |
| **Memory M5:** random/model behavior is not fixed-pi evidence | Labeled binary sibling only. | Labeled binary sibling only. | Labeled binary sibling only. |
| **Memory M6:** exact rational/finite data alone do not establish a pi frontier | Bounded gate is only a falsifier. | Bounded gate is only a falsifier. | Bounded gate and source theorem remain model-only. |

The comparator files are vendored and hashed in `SOURCE_PINS.md`.  T14, T37,
T49, T64, T67, and T83 are treated as checked local interfaces.  The semantic
obstruction memory is explicitly treated as an unverified note and only a
checklist.

## 7. Replay and final model-only conclusions

From a directory containing only these artifacts, run:

```text
python3 verify_models.py
sha256sum -c SHA256SUMS
```

`verify_models.py` checks 55 Thue--Morse and 55 period-doubling parameter pairs,
the displayed bounded examples, `|P_k|=4k` for `1<=k<=64`, the exact `P_7`
set, its 28 distinct blocks, the three noncanonical collisions, the first-48
energy `98`, and the canonical statement hash.  `raw_output.txt` records the
replayed output.  These finite checks test transcription and can falsify the
specific aligned, fiber-preserving, or representative-only implementations
named in the three rejection gates; they do not disprove the broader transfer
hypotheses, prove the universal source theorem, or prove any pi claim.

Final model-only verdicts:

| system | verdict | reason |
|---|---|---|
| Thue--Morse | **close** | exact synchronization uses changing aligned samples; same-mass energy does not decrement |
| period-doubling | **close** | substitution bias changes the constant but still fails the same-prefix T64 test |
| regular paperfolding | **hold as model** | exact carry/valuation collision atlas survives, but multiplicities and metric carry transfer are absent |

No claim is made for C1, C2, canonical A1, normality, decimal factor complexity
of pi, or local pi-digit occurrence.
