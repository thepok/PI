# T157: inverse Littlewood--Offord scout for block-difference vectors

Audit date: 2026-08-12 UTC.

The source statements retained below are `literature-checked` against four
pinned primary PDFs and the exact locators in `SOURCE_PINS.md`. Every
collision translation, substitution, comparison, and rejection in this report
is a `proof sketch`. The replay is an `experiment`: it checks hashes, caps,
markers, exact finite identities, and arithmetic substitutions, not a universal
theorem or any property of pi.

```text
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 8
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
PRIOR_COMPARISON_RANGE: T89-T154
PRIOR_COMPARISON_COUNT: 66
ACTIVE_COMPARISON_RANGE: T155-T156
ACTIVE_COMPARISON_COUNT: 2
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, provenance, and ambiguities

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

There is no original Erdos Problems URL. The immutable file records a local
formulation dated 2026-07-22. It asks whether, for every integer `A>=1`, every
sufficiently large depth `n` has some `N>=1` with
`A*n*Q_pi(n,N)<=N^2`, where `Q_pi` counts ordered, diagonal-inclusive strict
circle near returns of the fixed orbit `{10^j*pi}`. T157 neither changes nor
answers that question.

T157 audits the A10/A13/A14 sibling consisting of exact equality of overlapping
decimal blocks in an arbitrary finite word. The following quantifiers and
conventions are frozen before source substitution.

1. `M>=1` is the number of starts and `m>=1` is the block depth.
2. The word has length `L=M+m-1`; starts are exactly `0,...,M-1`.
3. Blocks neither wrap nor pad. The last block ends at `L-1`.
4. Collisions are ordered and include all `M` diagonal pairs.
5. The random signs introduced below are auxiliary independent Rademacher
   variables, not random digits and not random starts.
6. Source theorems about one deterministic coefficient vector do not average
   over block pairs unless an additional theorem explicitly supplies that step.
7. An applicability failure closes only the audited mechanism, not A1, C1,
   C2, T7, T107, or any assertion about pi.

## 2. Bounded clean-context search

The search stopped after six primary sources in the three required domains.
Four PDFs were retrieved and inspected. Two exact primary records were
inspected but their PDFs could not be retrieved without publisher challenges;
they are blockers and supply no retained mathematical claim.

| ID | domain | primary source | exact inspected locus | disposition |
|---|---|---|---|---|
| S1 | inverse concentration | Nguyen--Vu, *Optimal Inverse Littlewood-Offord theorems* | Theorems 2.1 and 2.5, printed pp. 6--7 | retained C-GAP |
| S2 | inverse concentration | Rudelson--Vershynin, *The Littlewood-Offord Problem and invertibility of random matrices* | Definition 1.4, Corollary 1.6, Theorem 4.1, printed pp. 6--7 and 20--21 | retained C-LCD |
| S3 | structured exponential sums | Ferber--Jain--Luh--Samotij, *On the counting problem in inverse Littlewood--Offord theory* | Theorem 1.4, Definition 1.5, Theorem 1.7, printed pp. 4--5; Theorem 1.1 on pp. 1--2 inspected only as the authors' Halasz restatement | retained C-HAL |
| S4 | inverse concentration | Tao--Vu, *A sharp inverse Littlewood-Offord theorem* | Theorems 1.9--1.10, printed pp. 4--5 | screened: superseded for this audit by S1 |
| S5 | symbolic collision theory | Guibas--Odlyzko, *String overlaps, pattern matching, and nontransitive games* | DOI record; journal pp. 183--208 | retrieval blocker; no claim retained |
| S6 | symbolic collision theory | Arratia--Waterman, *Critical Phenomena in Sequence Matching* | DOI record; Ann. Probab. 13(4) | retrieval blocker; no claim retained |

`SOURCE_PINS.md` gives the bounded query/disposition log, URLs, PDF and text
hashes, theorem/page ranges, and both retrieval failures. Search count is six,
below eight. Candidate count is three, at the cap. S5--S6 are counted as
inspected primary records but are not used as premises. No secondary survey is
counted.

## 3. Literal collision and signed concentration event

Let `D={0,...,9}` and let

```text
x=(x_0,...,x_(L-1)) in D^L,       L=M+m-1,
W_i^m(x)=(x_i,...,x_(i+m-1)),     0<=i<M.
```

Define the ordered block-collision statistic

```text
E_x(m,M)=#{(i,j) in {0,...,M-1}^2:W_i^m(x)=W_j^m(x)}.     (3.1)
```

If `c_x(w)=#{i<M:W_i^m(x)=w}`, then

```text
E_x(m,M)=sum_(w in D^m)c_x(w)^2.                          (3.2)
```

Thus (3.1) includes exactly `M` diagonal pairs. For each ordered pair `(i,j)`,
define the literal integer block-difference vector

```text
v^(i,j)=(x_i-x_j, x_(i+1)-x_(j+1),...,
         x_(i+m-1)-x_(j+m-1)) in {-9,...,9}^m.            (3.3)
```

Let `epsilon_0,...,epsilon_(m-1)` be independent uniform signs in `{+1,-1}`
and define the associated signed concentration event and atom probability

```text
C_(i,j)={sum_(t=0)^(m-1) epsilon_t v_t^(i,j)=0},
rho_(i,j)=sup_(a in Z) Pr(sum_t epsilon_t v_t^(i,j)=a).    (3.4)
```

The exact collision-to-concentration identity is

```text
W_i^m(x)=W_j^m(x)
  <=> v^(i,j)=0
  <=> Pr(C_(i,j))=1
  <=> rho_(i,j)=1.                                        (3.5)
```

The only nontrivial direction to check is `Pr(C)=1 => v=0`: if some
`v_s!=0`, fixing all other signs and flipping only `epsilon_s` changes the sum
by `2v_s`, so both sign assignments cannot equal zero. Consequently

```text
E_x(m,M)=sum_(0<=i,j<M) 1[rho_(i,j)=1].                   (3.6)
```

Equation (3.6), not a heuristic analogy, is the promised literal bridge. It
also exposes the degeneracy: every collision maps to the zero coefficient
vector and the largest possible atom. Inverse concentration can classify this
as additive structure only in the vacuous rank-zero sense.

### 3.1 Overlap dependence

For lag `d=j-i` with `0<d<m`, the coordinates in (3.3) obey

```text
v_t=x_(i+t)-x_(i+d+t),       0<=t<m.                      (3.7)
```

They share the `m+d` underlying digits and telescope:

```text
sum_(t=0)^(m-1) v_t
 =sum_(t=0)^(d-1)x_(i+t)-sum_(t=m)^(m+d-1)x_(i+t).        (3.8)
```

Inverse Littlewood--Offord theorems do not require coefficient independence,
so overlap does not invalidate their hypotheses by itself. It does invalidate
any unsourced step treating the family of pair-vectors as independent samples,
and (3.8) shows that their additive relations include deterministic boundary
telescoping rather than a new concentration-rigidity certificate.

## 4. Candidate C-GAP: optimal inverse Littlewood--Offord

### 4.1 Source statement and exact range

S1 Theorem 2.1 fixes constants `epsilon<1` and `C>0`. For an integer multiset
`V={v_1,...,v_n}` with Rademacher concentration `rho(V)>=n^(-C)`, it supplies a
proper symmetric GAP `Q` of rank `r=O_(C,epsilon)(1)` containing all but at
most `epsilon*n` elements, with

```text
|Q|=O_(C,epsilon)(rho(V)^(-1)*n^(-r/2)).                  (4.1)
```

Theorem 2.5, for `n^epsilon<=n'<=n`, replaces `epsilon*n` by `n'` and gives

```text
|Q|=O_(C,epsilon)(rho(V)^(-1)/(n')^(r/2)).                (4.2)
```

The source uses positive `C`; constants implicit in `O` are not explicit.

### 4.2 Literal substitution and failure

Set `n=m` and `V=V_(i,j)`, the coordinate multiset of (3.3). For a collision,
`rho(V)=1`. For every fixed positive `C`, the threshold `1>=m^(-C)` passes.
The theorem's conclusion is already satisfied by the exact minimal proper
symmetric GAP

```text
Q={0},        rank r=0,        |Q|=1.                     (4.3)
```

Substitution into (4.1) gives `1=O(1)`. This is quantitatively true for every
collision and distinguishes no word, lag, depth, or multiplicity. Taking any
positive rank is unnecessary and the theorem has no lower-rank exclusion.

For a noncollision, the theorem can constrain most coordinate differences
only when `rho_(i,j)>=m^(-C)`. Even if every noncolliding pair were shown to
have small concentration, (3.6) counts the pairs with `rho=1`; no implication
upper-bounds how many zero vectors occur. Summing the GAP conclusions over
`M^2` dependent pairs is not in S1.

**Quantitative rejection C-GAP:** at the exact collision value `rho=1`, the
output volume is one and rank zero, independently of `M`, while the desired
symbolic target would require an upper bound such as
`E_x(m,M)<=M^2/(A*m)`. The source conclusion has no `E_x` term and remains
identical for `E_x=M` and `E_x=M^2`.

## 5. Candidate C-LCD: essential least common denominator

### 5.1 Source statement and exact range

S2 Definition 1.4 defines `D_(alpha,kappa)(a)` for a real coefficient vector
as the infimum of `t>0` for which all but `kappa` coordinates of `t*a` lie
within `alpha` of nonzero integers. S2 Theorem 4.1 assumes

```text
1<=|a_k|<=K for every k,   0<alpha<1/(6K),   0<kappa<n,   (5.1)
```

and gives, for iid centered variables of variance at least one and third moment
at most `B`,

```text
p_eta(a)<=C*B*K^3/sqrt(kappa)
          *(eta+1/D_(2alpha,2kappa)(a))
          +C*exp(-c*alpha^2*kappa/B^2).                  (5.2)
```

Corollary 1.6 gives the inverse approximate-progression statement under the
same equal-order coefficient condition: if `p_eta(a)>=n^(-A)`, then all but
`kappa` coefficients are close to an arithmetic progression of length
`O(n^A*kappa^(-1/2))`, provided `eta` is no larger than the reciprocal length.

### 5.2 Literal substitution and failure

For `a=v^(i,j)`, every collision has `a_k=0`. Therefore the first hypothesis
in (5.1) fails in all `m` coordinates, not just a negligible exceptional set.
No rescaling repairs zero coefficients. The essential LCD definition also asks
for proximity to **nonzero** integers, so the zero vector has no finite witness.

For noncolliding pairs, delete the zero coordinates and put

```text
s_(i,j)=#{t<m:v_t^(i,j)!=0}.                              (5.3)
```

The remaining coefficients obey `1<=|a_k|<=9`, so `K=9` and any
`0<alpha<1/54` pass. The theorem then has `n=s_(i,j)`, not block depth `m`.
At small Hamming support, its unavoidable first scale is
`1/sqrt(kappa)` and cannot produce a factor `1/m`. More importantly, deleting
zeros has removed exactly the collision case counted in (3.6).

**Quantitative rejection C-LCD:** on every summand contributing to `E_x`, the
coefficient lower bound `1<=|a_k|` fails `m` times. On noncontributors, the
applicable dimension is only `s_(i,j)` and the theorem controls the small-ball
probability of that pair, not the number of zero pair-vectors. Thus there is no
legal substitution yielding any upper bound for (3.6).

## 6. Candidate C-HAL: additive-relation exponential sums

### 6.1 Source statement and exact range

For context only, S3 Theorem 1.1 records Halasz's integer inequality; it is not
retained as an original S3 theorem. For
`a in (Z\{0})^n` and integer `k>=1`, let `R_k(a)` count signed `2k`-term
relations with repeated indices. Then an absolute `C>0` satisfies

```text
rho(a)<=C*sqrt(k)*R_k(a)/(2^(2k)*n^(2k+1/2))
        +exp(-n/max(k,C)).                                 (6.1)
```

The retained S3 Theorem 1.4 gives a finite-field version for odd prime `p`, nonzero
`a in F_p^n`, and parameters satisfying

```text
30*M<=|supp(a)|,       80*k*M<=n,                         (6.2)
```

with

```text
rho_Fp(a)<=1/p+C*R_k(a)/(2^(2k)*n^(2k)*sqrt(M))+exp(-M).  (6.3)
```

The retained S3 Theorem 1.7 is a direct counting theorem for finite-field vectors whose
every large subvector has many nondegenerate relations. Its object is a set of
coefficient vectors in `F_p^n`, not overlapping digit words.

### 6.2 Literal substitution and failure

Set `n=m` and `a=v^(i,j)`. For a collision, `a=0`; the contextual Theorem 1.1
excludes it through `a in (Z\{0})^n`, and retained Theorem 1.4 excludes it through
`a!=0` and (6.2), whose left side is positive while support is zero.

Ignoring that illegal substitution illustrates why relations do not help. For
the zero vector every signed indexed tuple is a relation, hence

```text
R_k(0)=2^(2k)*m^(2k).                                     (6.4)
```

Putting (6.4) into the main term of (6.1) yields

```text
C*sqrt(k)*R_k(0)/(2^(2k)*m^(2k+1/2))
 =C*sqrt(k/m).                                             (6.5)
```

At `k=1`, this is only `C/sqrt(m)`, while the actual atom is one; the source
hypothesis failure is therefore essential. At `k` comparable with `m`, the
bound is constant-scale and still does not count how many pairs have `a=0`.

The finite-field counting theorem also cannot be substituted. Mapping a word
to all `M^2` vectors (3.3) is highly noninjective; constant words send every
pair to the same zero vector. Counting coefficient vectors thus erases the
fiber multiplicity equal to `E_x`.

**Quantitative rejection C-HAL:** every collision has support zero, violating
(6.2) by `30M` positions for every `M>0`; the formal relation count is maximal
as in (6.4), not an anti-concentration certificate. The source counting theorem
counts images, whereas the desired statistic is precisely the total size of
their zero-vector fibers.

## 7. Universal kill tests

These examples are elementary `proof sketch` checks of the substitution, not
claims about pi.

1. **Constant word.** If every digit is zero, every `v^(i,j)=0`, every signed
   event has probability one, and `E_x=M^2`. C-GAP always returns `{0}`;
   C-LCD and C-HAL fail their nonzero/support hypotheses.
2. **Period `p`.** For a primitive period-`p` word and `M` divisible by `p`,
   once `m>=p`, there are `p` block types of multiplicity `M/p`, so
   `E_x=M^2/p`. Every equal-phase pair again maps to zero. None of the three
   candidate outputs records `p` or the number of equal-phase pairs.
3. **Repeated de Bruijn period.** Repeating a decimal de Bruijn cycle of order
   `r` with `M` a period multiple gives `E_x=M^2/10^r` for every `m>=r`.
   The low-order block law may be perfectly uniform while all colliding pairs
   still map to the same rank-zero vector.
4. **Shared prefix.** If the first `R+m-1` digits are equal, the first `R`
   starts give `R^2` collisions at depth `m`; the inverse theorem is invoked
   `R^2` times on the identical zero vector and creates no additive saving.
5. **One-symbol mismatch.** If a pair-vector has support one with coefficient
   `d!=0`, then `rho=1/2`, regardless of `m`. C-LCD applies only in dimension
   one after zero deletion; C-HAL's support condition fails for every useful
   `M`; neither produces a depth-dependent block-pair count.

The first four tests separate collision multiplicity from coefficient
structure. The fifth shows that even near-collisions with sparse difference
support have effective Littlewood--Offord dimension `s`, not block depth `m`.

## 8. Complete T89--T156 comparison

`PRIOR_INDEX.md` contains one normalized row for every item T89--T156, with
verification level, exact comparator path and SHA-256, fingerprint, and T157
boundary. It mechanically contains 66 prior rows T89--T154 and two active rows
T155--T156.

No comparison deduction is imported as a theorem. Items under `notes/` are
unverified sketches and are cited only as fingerprint warnings. The mandatory
exclusions are:

| item(s) | excluded fingerprint | T157 boundary |
|---|---|---|
| T105 | additive energy, BSG, flattening, prescribed-character failure | T157 never uses additive energy of the full decimal difference set; it tests Rademacher concentration of each literal block-coordinate difference vector |
| T114 | interpolation determinant, rank, and height | no determinant or arithmetic nonvanishing is used |
| T119 | predictive/Hankel/Prony rank | rank-zero GAP output is a vacuous source conclusion, not a predictive-rank inference |
| T131 | de Bruijn-flow rounding and Euler tours | de Bruijn words appear only as a kill test; no flow construction or census is claimed |
| T140 | hypergraph container census | no container, supersaturation, or codegree theorem is used |
| T144 | one-depth residue method-of-types census | no residue extraction or type count is used |
| T147 | shared-prefix multidepth counterfamily | used only as an independently rechecked kill specification; no census conclusion is imported |
| T150 | reuse-adjusted bounded-differences census | no Gibbs law or concentration over words is used |
| T152 | depth-localized fractional-cover census | no entropy charging or Shearer inequality is used |
| T153 | logarithmic locality / k-Abelian flow | T157's coordinate-vector concentration is not short-factor equivalence |
| T154 | reuse-capacity entropy LP | no interval packing or dual entropy charge is used |

### 8.1 Active T155/T156 boundary

The refreshed runtime provides only active lease identifiers for T155 and T156,
recorded byte-exactly in `active_items_snapshot.json`. It provides no agenda,
title, report, theorem, source, or normalized mathematical fingerprint for
either item. Repository-wide comparison found no readable T155/T156 artifact.

Accordingly T157 reserves and excludes both item identifiers and makes **no
nonduplication claim against unavailable mathematical content**. This is the
complete honest comparison possible from the supplied active snapshot. Neither
T157's candidate novelty nor its negative conclusion depends on distinction
from T155/T156: all three candidates fail independently at the literal
zero-vector/support gate.

### 8.2 Retained source/theorem tuple novelty

The three retained normalized tuples are:

```text
C-GAP = (S1 PDF SHA, Theorems 2.1+2.5, pairwise block-difference GAP output)
C-LCD = (S2 PDF SHA, Definition 1.4+Corollary 1.6+Theorem 4.1,
         pairwise block-difference essential-LCD output)
C-HAL = (S3 PDF SHA, Theorems 1.4+1.7 and Definition 1.5,
         pairwise signed-relation/support output)
```

`verify_t157.py` checks these keys are distinct and absent from the normalized
mechanism strings and report hashes of all readable prior rows. This is a
bounded ledger comparison, not a claim of mathematical novelty in the
literature.

## 9. Additional unproved pi-specific transfer premises

The following are separate `conjecture`-level premises. They are not asserted,
and none is supplied by S1--S6.

**Toward T7.** For actual pi-orbit blocks

```text
B_(i,m)(pi)=floor(10^m*{10^i*pi}),
```

one would need an independent theorem `PI-ILO-FIBER` stating, with T7's exact
quantifiers, that for every required `(A,m)` there is an `N` such that the
number of ordered pairs whose literal digit-difference vector is zero is at
most `N^2/(A*m)` (or another independently proved implication with that
conclusion). This is exactly a fixed-pi zero-fiber bound. It is unproved; if
assumed in this form it is the symbolic collision input, not a consequence of
inverse Littlewood--Offord theory.

**Toward T107.** One would additionally need an independent fixed-pi theorem
`PI-ILO-ROWS` converting nonzero pair-vector structure on one increasing prefix
sequence into both T107 triangular requirements on a positive-density family:

```text
rowBoundaryLoad(ell,N)<=N/(40*10^ell),
|rowFourierRemainder(ell,N)|<=N^2/(10*10^ell).             (9.1)
```

This transfer is unproved. Rademacher concentration in the coordinate index
does not evaluate the prescribed decimal Fourier character, and no retained
source contains (9.1). Assuming (9.1) would supply the missing T107 analytic
premise rather than derive it.

There is no fixed-pi, A1, C1, or C2 claim. Even a proved symbolic zero-fiber
bound would still require the already named and independently proved interface
before any canonical metric conclusion.

## 10. Replay and endpoint

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t157.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes; PDF page counts and text
anchors; the six-source/eight-source and three-candidate caps; all 68 T89--T156
rows and comparator pins; the exact active-item snapshot; unique candidate
keys; ordered diagonal collision identities; collision-to-concentration by
complete sign enumeration; periodic/de-Bruijn/shared-prefix/sparse-support kill
tests; every displayed candidate substitution; one verdict, zero successors,
and the transfer/claim firewall. Finite replay is an experiment only.

SCOPED_VERDICT (1/1): **close**.

This closes only the audited attempt to use inverse Littlewood--Offord,
essential-LCD, or signed-relation structure of the literal overlapping
block-coordinate difference vectors to upper-bound ordered block collisions.
Exact collisions are precisely zero vectors, so C-GAP is already satisfied by
the vacuous rank-zero progression and C-LCD/C-HAL exclude the contributing vectors through
nonzero or support hypotheses. None counts the multiplicity of the zero fiber,
and no legal quantitative substitution reaches a `1/m` collision bound. This
does not close other inverse-concentration encodings, does not falsify a
symbolic census, and implies nothing about pi, A1, C1, C2, T7, or T107.

No successor is proposed.
