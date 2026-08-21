# T162: deterministic path-order reconstruction scout

Audit date: 2026-08-12 UTC.

Statements attributed to S1--S3 and pinned in `SOURCE_PINS.md` are
`literature-checked`. Definitions, substitutions, separator deductions, and
applicability conclusions in this report are `proof sketch`. Output of
`verify_t162.py` is a finite-test `experiment`, never a universal proof. The
fixed-pi certificate in Section 9 is a separate `conjecture` and `unproved pi
transfer`; it is not asserted.

```text
PRIMARY_SOURCE_COUNT: 3
PRIMARY_SOURCE_CAP: 8
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
SEPARATOR_TEST_COUNT: 5
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable question and normalized scope

The canonical question was formulated by this program on 2026-07-22; it has
no external source URL. The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It fixes `pi`, decimal powers, strict circle distance, ordered pairs including
diagonals, and quantifiers `forall A exists n0 forall n>=n0 exists N`.
T162 instead audits exact equality of finite symbolic blocks, the weaker A10
sibling, and related fixed-point/automatic models under A13--A14. It makes no
transfer to the canonical metric count.

Ambiguous terms are fixed as follows.

1. `M` is the number of starts, `m` the target depth, and the finite word has
   exactly `M+m-1` digits; starts are `0,...,M-1`, nonwrapping and unpadded.
2. A short empirical Markov type of order `r<m` is the complete vector of
   length-`r+1` transition multiplicities plus its initial and terminal
   length-`r` states. It records no Euler ordering.
3. Logarithmic depth means `1<=m<=floor(kappa log_10 M)` for one stated fixed
   `kappa>0`; every candidate must be uniform throughout this range.
4. A deterministic certificate must apply to the specified word. A theorem
   about a sampled path, invariant measure, or constructed fixed point is a
   related model only.
5. Maximum occupancy alone, global `L2`, graph conductance, run counts, and
   hypotheses equivalent to T7 collision decay or T107 triangular Fourier
   control are forbidden premises.

## 2. Exact target and the order-sensitive invariant

For a decimal word `x_0...x_(M+m-2)`, put

```text
W_i^m=x_i...x_(i+m-1),
c_m(w)=#{0<=i<M:W_i^m=w},
E_m=sum_(w in D^m)c_m(w)^2.                              (2.1)
```

Expanding squares, `E_m` is the ordered, diagonal-inclusive equal-block pair
count. Since `sum_w c_m(w)=M`,

```text
E_m <= M*Cmax_m,       Cmax_m=max_w c_m(w).              (2.2)
```

Define the occurrence set and minimum return gap

```text
Occ_m(w)={i in [0,M):W_i^m=w},
g_m=min{|i-j|:i!=j and W_i^m=W_j^m},                     (2.3)
```

with `g_m=infinity` if there is no repeated block. This is order-sensitive:
it uses the actual positions of equal paths, not only transition
multiplicities. If a set of integers in `[0,M)` has pairwise gaps at least
`g`, its size is at most `1+floor((M-1)/g)`. Therefore

```text
Cmax_m <= 1+floor((M-1)/g_m) <= 1+M/g_m.                 (2.4)
```

For a slack parameter `K>=2`, the candidate certificate is

```text
SEP(K,A,M,m):  M>=K*A*m  and  g_m>=K*A*m.                (2.5)
```

Substitution of every constant gives

```text
Cmax_m <= 1+M/(K*A*m)
       <= M/(K*A*m)+M/(K*A*m)
        =2M/(K*A*m)
       <= M/(A*m),                                      (2.6)
E_m <= M*Cmax_m <= M^2/(A*m).                           (2.7)
```

Thus minimum return separation is a sufficient deterministic mechanism and
is strictly cheaper to falsify than estimating all occupancies. It is not a
new theorem: (2.4)--(2.7) are elementary deductions. No inspected source
proves `SEP` for arbitrary words or for pi.

Endpoint range: `W_(M-1)^m` ends at `M+m-2`, exactly the final supplied digit.
No cyclic closure is used in (2.3). Logarithmic range: the candidate is tested
at a selected `1<=m<=floor(kappa log_10 M)` with constants independent of
`m`. A stronger triangular version would require (2.5) simultaneously at all
depths in that range. None of S1--S3 supplies even the selected-depth bound.

## 3. Exclusion ledger through T161

`EXCLUSION_LEDGER.csv` contains one consecutive row for every item T89--T161.
Rows T89--T157 preserve T158's accepted preselection ledger. The refreshed
rows are:

- T158 is accepted changed evidence (`LC/PS/EXP`): its repeated order-`r+1`
  de Bruijn word has exact short transition census and positive pseudo-gap but
  long-block occupancy `M/10^(r+1)`. Transition expansion and conductance are
  excluded.
- T159 is indexed as an unverified `PS/EXP` note, but its file is absent from
  this clean context's supplied knowledge directory. The index describes an
  iid Palm--Stein model; T162 imports no claim from that description.
- T160 is pipeline-revised/unavailable: the refreshed result records a failed
  delivery because its declared artifacts were missing. Pair-multiplicity
  recurrences are reserved and not duplicated; no mathematical claim is
  imported from the failed delivery.
- T161 is now indexed as an accepted `PS/EXP` note (verification `sketch`),
  replacing the inherited active/unavailable label. Its stochastic-clustering
  argument remains unverified exploration and is not imported as a discharged
  premise. The indexed report hash is
  `48ede4b571568c5e088c024687037a1d5b864cf3a27ff11f55136cf811ca7d79`;
  the file itself is not present in this clean context's supplied knowledge
  directory, so T162 reserves the lane and infers no theorem from it.

The ledger also explicitly excludes maximum occupancy as a premise, global
`L2`, conductance, run counts, T7-shaped collision premises, and T107-shaped
triangular Fourier premises. The duplication boundary is narrow: T153 already
identified that short k-Abelian/de Bruijn census loses ordering, and T158
strengthened the separator to an expanding empirical kernel. T162 does not
repeat either claim; it asks whether one of three source-native invariants
directly retains the missing order and records its first quantitative failure.

## 4. Bounded three-source scout

Exactly three previously unaudited primary sources were inspected, below the
cap of eight, and exactly three candidates were retained, at the cap of three.
Hashes, URLs, and theorem locators are in `SOURCE_PINS.md`.

| Card | Lane | Order-sensitive invariant | Decision |
|---|---|---|---|
| C-RET | symbolic collision theory | actual minimum return gap `g_m` | sufficient as an elementary related-model certificate; source substitution fails at minimum-versus-maximum return |
| C-DER | named fixed-point dynamics | derivated word ordering return-word types | preserves order but source supplies no quantitative occurrence gaps or logarithmic-depth uniformity |
| C-AUT | short structured exponential sums | interval correlations after carry-aware differencing | theorem applies to automatic coefficients and rational phases, not block indicators of a prescribed orbit; first phase mismatch |

No source is counted twice. Previously audited Durand, k-Abelian, Markov,
global Fourier, and Euler-tour papers were not reopened or counted.

## 5. Candidate substitutions and first failed inequalities

### 5.1 C-RET: minimum return separation

S1 Definition 39 and Observation 40 state

```text
R_u(m)=max{|r|:r return word to an m-factor}+m-1.         (5.1)
```

Lemma 41 reduces that maximum to suitable bispecial factors, and Theorem 54
computes `R_u` for CS Rote sequences. These are order-aware statements.
However, (2.4) needs the opposite endpoint:

```text
g_m = min{|r|:r is a return word between equal m-blocks}. (5.2)
```

The first failed inequality is

```text
S1 gives max_return(m)=R_u(m)-m+1;
needed: min_return(m)=g_m >= K*A*m.                       (5.3) FAIL
```

No upper bound on `max_return` lower-bounds `min_return`. Critical exponent
control also bounds powers/overlap geometry but does not make (5.3) uniform
for all factors and logarithmically growing `m`. C-RET is therefore a valid
related-model deduction only when `SEP` is independently verified.

### 5.2 C-DER: derivated fixed-point ordering

S2 Section 2.1 uniquely codes a uniformly recurrent word as its ordered
concatenation of return words. Theorem 25 classifies derivated words of a
primitive Sturmian fixed point as fixed points of iterated morphisms; Example
27 identifies the Fibonacci self-derivation, and Corollary 35 bounds the
number of derivated words by `3|w|-4` for normalized morphism name `w`.

Define, for prefix `p`, return words `r_0,...,r_(q-1)` and derivated word
`d_p=s_0s_1...`,

```text
G_p(T)=min{|r_(s_j)|:0<=j<T},                             (5.4)
H_p(T)=max_a #{0<=j<T:s_j=a}.                            (5.5)
```

For the finite prefix ending at digit `M+m-2`, only complete return words
whose two delimiting occurrences of `p` start in `[0,M)` are counted; a final
incomplete return word is retained as an endpoint defect and cannot certify a
gap. Set `m=|p|` with selected-depth range
`1<=m<=floor(kappa log_10 M)`. The source fixes one infinite Sturmian word and
one prefix at a time; it states no constants uniform over this growing range.

`d_p` retains order, and `G_p` is an actual geometric gap. For target depth
`m=|p|`, the needed first step is

```text
G_p(T) >= K*A*m for every return type seen before M.      (5.6) FAIL
```

S2 classifies which morphism generates `d_p`; it supplies neither (5.6), a
bound on `H_p(T)`, nor constants uniform for `m<=kappa log_10 M`. Adding a
bound on `H_p` strong enough to imply (2.6) would merely rename maximum
occupancy and is forbidden. C-DER is retained as an order-preserving model,
not as an occupancy implication.

### 5.3 C-AUT: carry-aware interval correlations

S3 Theorem 1 bounds `sum_(n in I) a_n e_q(f(n))` for an automatic sequence
`a_n`, rational phase `f`, and explicit squarefree modulus component `q_1`.
It is nontrivial in the Polya--Vinogradov range `|I|>=q^(1/2+epsilon)` and is
explicitly trivial for linear or constant `f`. Definition 2 supplies a carry
property, while Proposition 1 reduces an automatic weighted sum to two-point
phase correlations `U(x,y;h;q,a)` subject to `R*M0^2<=x/10` (here `M0` is S3's
base-power parameter, not our number of starts).

The finite endpoint range would take the exact integer interval
`I={0,...,M-1}` and a supplied word through digit `M+m-2`; every block
indicator uses only those `M` starts. The selected target depth must satisfy
`1<=m<=floor(kappa log_10 M)`, while S3's source range instead constrains the
phase interval by the Polya--Vinogradov condition and does not contain a block
depth parameter. Thus its stated uniformity cannot be reinterpreted as
uniformity in growing `m`.

For a target word `w`, Fourier inversion of its block indicator would first
require a sourced uniform estimate

```text
|sum_(i<M) 1[W_i^m=w] - M/10^m| <= M/(2*K*A*m)           (5.7)
```

for all `w` and logarithmic `m`. But the coefficient sequence
`1[W_i^m=w]` of a prescribed decimal orbit is not supplied as one fixed
automatic sequence, and its needed phases are digit-cylinder characters, not
S3's rational `e_q(f(n))`. Thus the first failed step is the hypothesis match
before any exponent or constant can be substituted. Assuming (5.7) would be a
maximum-occupancy premise under Fourier notation; assuming the all-frequency
square sum is global `L2`; both are excluded.

## 6. Five separator tests

Every test uses (2.1)--(2.5), not a transition graph.

### SPT1 constant

For `x=0^(M+m-1)`, every start has the same block, so `g_m=1`,
`Cmax_m=M`, and `E_m=M^2`. `SEP` rejects whenever `K*A*m>1`.

### SPT2 primitive-periodic

Let a primitive word of period `p` be repeated with enough look-ahead and take
`M=Jp` starts. If `J=1`, then for `m>=p` the `p` phase blocks are distinct, so
`g_m=infinity`, `Cmax_m=1`, and `E_m=p`; no recurrence gap exists inside the
one-period start window. If `J>=2`, every phase occurs at least twice, equal
phase blocks recur first at gap `p`, and for `m>=p`

```text
g_m=p, Cmax_m=J=M/p, E_m=p*J^2=M^2/p.                    (SPT2)
```

Thus `SEP` rejects when `J>=2` and `p<K*A*m`. This is stronger than a run
count: a run-free alternating word with at least two periods of starts still
has `g_m=2`.

### SPT3 repeated de Bruijn

Repeat a decimal de Bruijn cycle of order `r+1`, period `p=10^(r+1)`, and use
`M=Jp` starts. T158's changed evidence gives exact short census and an
expanding associated kernel. For `J=1` and `m>=r+1`, the `p` phase blocks are
distinct, so `g_m=infinity`, `Cmax_m=1`, and `E_m=p`. For `J>=2`, every phase
occurs at least twice and actual equal long paths first recur every `p`:

```text
g_m=p, Cmax_m=J=M/p, E_m=p*J^2=M^2/p
    for J>=2 and m>=r+1.                                  (6.1)
```

When `J>=2` and `K*A*m>p`, `SEP` rejects exactly where transition expansion
fails to control occupancy. Thus C-RET detects the missing ordering
discriminator. The `J=1` qualification is essential: with only one period of
starts there is no repeated phase and hence no finite return gap.

### SPT4 shared prefix

If the first `R+m-1` symbols are zero, then starts `0,...,R-1` share `0^m`.
Therefore `g_m=1`, `Cmax_m>=R`, and `E_m>=R^2`, regardless of a uniform or
expanding suffix. `SEP` rejects. It does not accept a vanishing short-census
error or positive suffix conductance as a substitute.

### SPT5 bounded multi-core

Concatenate `B<=B0` periodic cores. If any core contributes two equal
`m`-blocks at positions separated by core period `p_b<K*A*m`, then
`g_m<=p_b` and `SEP` rejects. If every repeated target block across all cores
has gap at least `K*A*m`, (2.4) applies globally, including cross-core pairs;
the number of cores does not introduce a missing factor. This test uses actual
positions and endpoints, not graph disconnection or conductance.

```text
SEPARATOR_CONSTANT: reject-gap
SEPARATOR_PRIMITIVE_PERIODIC: reject-period-gap
SEPARATOR_REPEATED_DEBRUIJN: reject-order-gap
SEPARATOR_SHARED_PREFIX: reject-prefix-gap
SEPARATOR_BOUNDED_MULTICORE: reject-or-certify-global-gap
```

## 7. Excluded surrogates

- `Cmax_m<=M/(A*m)` is the desired occupancy bound itself, not a mechanism.
- `E_m<=M^2/(A*m)` or an equivalent Parseval identity is T7-shaped global
  `L2`, excluded as circular.
- Conductance and pseudo-gap belong to T158's rejected transition-kernel
  route and fail SPT3.
- Run counts fail primitive periodic and run-free alternation.
- T107's triangular Fourier and boundary budgets are stronger separate
  premises, not reconstructed here.
- C-RET is not equivalent to T7: `SEP` is sufficient but not necessary.
  Many moderately frequent blocks can make `E_m` small while some two
  occurrences are adjacent, so `g_m=1` and `SEP` fails.

## 8. Label-separated findings

**Literature-checked:** S1 computes maximum return lengths for CS Rote models;
S2 classifies derivated words of primitive Sturmian fixed points; S3 bounds
automatic coefficients against rational periodic phases in its stated range.

**Related-model proof sketch:** minimum return separation (2.5) implies the
collision target by (2.4)--(2.7). S1 and S2 show natural order-aware data
structures in uniformly recurrent fixed-point systems but do not establish
the needed minimum gap.

**Finite-test experiment:** `verify_t162.py` enumerates bounded words and
checks (2.4), (2.7) under `SEP`, and the five displayed separator families.
This is falsification support only.

## 9. Separate unproved pi transfer

**PI-PATH-ORDER-T162 (`conjecture`; UNPROVED PI TRANSFER; NOT ASSERTED).** For
each integer `A>=1` and all sufficiently large depths `m`, there is one
increasing family of actual pi prefixes with lengths `M=M(m)` and one fixed
`K>=2` such that

```text
M>=K*A*m,
min{|i-j|:0<=i<j<M and the length-m decimal blocks of pi at i,j agree}
  >=K*A*m.                                                (9.1)
```

This is the missing arithmetic path-order certificate on one increasing
prefix family. If (9.1) held, (2.7) would give a symbolic equal-block bound.
No inspected source proves (9.1), and symbolic equality is still weaker than
the canonical metric near-return count. There is no fixed-pi, A1, C1, or C2
claim.

## 10. Endpoint

`SCOPED_VERDICT (1/1): hold as model`.

Hold minimum return separation as an order-sensitive related-model
discriminator. It survives T158's repeated-de-Bruijn challenge in the useful
sense that it rejects the false transition-graph inference, and it has a
constant-explicit implication to collision decay. Do not develop it as a
fixed-pi route without new arithmetic input: the inspected return-word
theorems control maximum returns or classify return-type order, not the
required minimum gap, while the exponential-sum theorem has the wrong
coefficient and phase hypotheses.

`SUCCESSOR (0/1): none`.

From a directory containing only delivered artifacts, run:

```bash
python3 verify_t162.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The replay is an `experiment`; it checks artifact structure and bounded
examples, not the universal proof-sketch deductions.
