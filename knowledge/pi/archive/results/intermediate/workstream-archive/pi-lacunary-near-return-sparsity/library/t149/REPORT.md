# T149: weighted nonbinary three-point PSD applicability audit

Audit date: 2026-08-12 UTC.

The two retained source statements are `literature-checked` against the four
delivered primary PDFs and exact locators in `SOURCE_PINS.md`. The weighted
translation, identities, counterfamilies, and applicability conclusions are a
`proof sketch`: every step is written out below, but there is no Lean artifact.
The replay is an `experiment` checking hashes and finite instances, never a
proof of an asymptotic claim. This report makes no fixed-pi, A1, C1, or C2
claim.

```text
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 5
RETAINED_THEOREM_COUNT: 2
RETAINED_THEOREM_CAP: 2
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, scope, and ambiguous quantifiers

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

Canonical A1 asks whether, for every integer `A>=1`, every sufficiently large
`n` has some `N>=1` with `A*n*Q_pi(n,N)<=N^2`. The count uses the fixed orbit
`{10^j*pi}`, circle distance, a strict cutoff, ordered pairs, and every
diagonal pair. T149 instead audits equality of overlapping symbolic blocks.
It is therefore the weaker A10/A13 sibling even when its digits are taken from
pi. A bounded or artificial-word check is also A14.

Quantifiers frozen here are: `A>=1`, depth `m>=1`, number of legal starts
`M>=1`, and a word of exactly `L=M+m-1` digits. The universal mechanism claim
being tested would have to apply for growing `m`, not one fixed `m`, and would
have to preserve multiplicities. Counterfamilies may choose `M` as a function
of `m`; that is enough to refute a universal implication. Nothing here changes
the `forall A exists n0 forall n exists N` quantifiers of A1.

## 2. Exact weighted base-10 model and endpoints

Let `D={0,...,9}` and

```text
x=(x_0,...,x_(L-1)) in D^L,        L=M+m-1,
W_i^m=(x_i,...,x_(i+m-1)),         0<=i<M.
```

Starts neither wrap nor pad. The last legal block starts at `M-1` and ends at
`M+m-2=L-1`. Give start `i` a nonnegative weight `a_i` and put

```text
A_w = sum_(0<=i<M) a_i 1[W_i^m=w],       S=sum_i a_i,
E_m(a)=sum_(w in D^m) A_w^2.                         (2.1)
```

Expanding squares gives

```text
E_m(a)=sum_(0<=i,j<M) a_i*a_j*1[W_i^m=W_j^m].        (2.2)
```

Thus pairs are ordered and all weighted diagonal terms `sum_i a_i^2` are
included. The decimal-block multiset is the unweighted specialization
`a_i=1`, with multiplicities

```text
c_w=#{0<=i<M:W_i^m=w},   sum_w c_w=M,
E_m=sum_w c_w^2.                                      (2.3)
```

No support set replaces `(c_w)`: doing so would erase the quantity audited.

### 2.1 Exact prefix/suffix overlap balance

For `u in D^(m-1)`, define `U_j=(x_j,...,x_(j+m-2))` for `0<=j<=M` (for
`m=1`, `u` is the unique empty word). Directly shifting the suffix sum gives

```text
sum_(b in D) A_(ub) - sum_(b in D) A_(bu)
 = a_0 1[U_0=u] - a_(M-1) 1[U_M=u]
   + sum_(j=1)^(M-1) (a_j-a_(j-1)) 1[U_j=u].          (2.4)
```

Indeed, the first sum is `sum_(j=0)^(M-1)a_j 1[U_j=u]`
and the second is `sum_(j=1)^M a_(j-1)1[U_j=u]`.
For uniform start weights this is the exact endpoint convention

```text
sum_b c_(ub)-sum_b c_(bu)=1[U_0=u]-1[U_M=u].          (2.5)
```

There is no stationarity assumption. Cyclic balance occurs only when the two
endpoint `(m-1)`-words agree, as they do in the periodic counterfamilies below.

## 3. Weighted three-point variables and moment matrices

Put `Omega=D^m`, `p_w=c_w/M`, and use Hamming distance on `Omega`. For an
ordered triple `(r,s,t)` define the source's orbit parameters

```text
i=d(r,s), j=d(r,t),
u=#{v:r_v!=s_v and r_v!=t_v},
v=#{v:r_v!=s_v=t_v}.
```

Then `d(s,t)=i+j-u-v`. Define the multiplicity-preserving ordered triple
variables

```text
Lambda_(i,j,u,v)
 = sum_(r,s,t in Omega) c_r*c_s*c_t
     1[(r,s,t) has parameters (i,j,u,v)],              (3.1)
tau_(i,j,u,v)=Lambda_(i,j,u,v)/M^3.                    (3.2)
```

Repeated words and all three diagonal coincidences remain present, and
`sum Lambda=M^3`. These are the literal weighted analogues of S1 equation
(44); when every occupied word has multiplicity one, they reduce to S1's
ordered code triple counts.

For clarity, the weighted PSD extension used in this audit is derived rather
than attributed to S1. For each root `r`, choose a Hamming automorphism
`sigma_r` sending `r` to `0`, let `H` be the stabilizer of `0`, and regard
`p=(p_w)_(w in Omega)` as a column vector. Define

```text
R_p = sum_(r in Omega) p_r * |H|^(-1) sum_(h in H)
        (h sigma_r p)(h sigma_r p)^T.                   (3.3)
```

Here automorphisms only permute coordinates of `p`. Every summand is a
nonnegative multiple of a rank-one Gram matrix, hence `R_p` is PSD. Averaging
makes it Hamming-stabilizer invariant; its invariant coefficients are linear
combinations of the `tau` in (3.2). S2 Theorems 6 and 8 may therefore block
diagonalize this already-PSD matrix. This is a valid weighted principal
matrix, but not S1's complement matrix `R'`: S1 Proposition 8 uses the 0/1
set complement and `q^m-|C|`, which have no multiplicity analogue here.

More generally, for any finite real feature family `f_alpha:Omega->R`,

```text
G_(alpha,beta)=sum_w p_w f_alpha(w)f_beta(w)             (3.4)
```

is PSD because `z^T G z=sum_w p_w(sum_alpha z_alpha
f_alpha(w))^2>=0`. These are generic Gram moment matrices at the audited block
depth. Their positivity is universal for empirical laws and therefore cannot
by itself distinguish a collision-rich word. In Section 5.3, "order `r`"
means only contiguous subblock features measurable from length-`ell` words
for `ell<=r`; no claim is made about arbitrary nonlocal coordinate probes.

The key numerical identity is

```text
trace(R_p)=sum_w p_w^2=E_m/M^2.                         (3.5)
```

Automorphisms preserve Euclidean norm, and the root weights sum to one, so
(3.5) follows term by term. PSD says only that this trace is nonnegative; it
does not upper-bound it.

## 4. Candidate audit

### 4.1 C-3PSD: S1 equations (36)-(50), Propositions 8-9

| audit field | result |
|---|---|
| base | Source allows every `q>=3`; `q=10` is legal. |
| object | Source uses a set `C subset D^m`, not a multiset. |
| multiplicities | Ordered triple repetitions are counted, but `c_w>1` is not represented. Collapsing to support loses `E_m`. |
| growing depth | The theorem holds separately for every length `m`; it supplies no estimate uniform in growing `m`. |
| endpoints/overlap | Code coordinates have no start endpoints. Equations (2.4)-(2.5) are extra constraints not used by S1. |
| quantitative output | SDP upper-bounds the cardinality of a minimum-distance code. Equal-block collision has distance zero and is controlled by multiplicity, not code cardinality. |
| verdict inside audit | Does not yield `E_m<=M^2/(A*m)`. |

Even imposing positive minimum distance on the support does not bound a
single word's multiplicity. Tagging repeated copies would change the alphabet
or length and Hamming distances, so it is not a base-10 translation.

There is one exact non-universal implication, but it is not supplied by S1:

```text
max_w c_w <= M/(A*m)
  ==> E_m=sum_w c_w^2 <= (max_w c_w)sum_w c_w
      <= M^2/(A*m).                                     (4.1)
```

Its cheap kill test is one histogram pass: compute `max_w c_w` and reject as
soon as it exceeds `M/(A*m)`. Equivalently, (4.1) assumes min-entropy at least
`log(A*m)`. This is direct block anti-concentration, not a consequence of
three-point PSD, so C-3PSD is not retained as a survivor.

### 4.2 C-BLOCK: S2 Theorems 6 and 8, equations (57)-(61)

| audit field | result |
|---|---|
| base | The nonbinary example explicitly covers `q>=3`, hence base 10. |
| object | Arbitrary matrices in `Sym^m(B)`; no set or multiset theorem. |
| multiplicities | Weighted coefficients are allowed algebraically only after a valid matrix such as (3.3) is independently built. |
| growing depth | It gives a block decomposition at each `m`, with no cross-depth estimate. |
| endpoints/overlap | Neither endpoint balance nor overlapping starts occur in the theorem. |
| quantitative output | A star-isomorphism preserves PSD; it preserves rather than bounds the trace (3.5). |
| verdict inside audit | Does not yield `E_m<=M^2/(A*m)`. |

The same atom cap (4.1) would quantitatively finish the energy estimate, with
the same histogram kill test, but C-BLOCK supplies no route to that cap. It is
useful computational infrastructure for a separately justified inequality,
not a collision mechanism, and is not a survivor.

### 4.3 Screened lanes

S3 Theorem 1.5 concerns self-similar measures under affine irreducibility and
a Diophantine contraction-ratio hypothesis. An empirical overlapping-block
law has no supplied IFS or such hypothesis, and scalar Fourier decay is not a
three-point moment inequality. S4 Theorem 1 has the wrong direction at the
decimal grid: spacing `10^(-m)` costs `10^m`, while combining repeated labels
puts `sum c_w^2=E_m` into its coefficient norm. Neither source is a theorem
candidate after the literal base-10 substitution.

## 5. Three universal obstruction families

Each family uses an infinite periodic digit sequence only to provide the
finite prefix of length `L=M+m-1`; the legal starts remain the nonwrapping
`0,...,M-1` from Section 2.

### 5.1 Constant word: universal PSD cannot control energy

Take `x_j=0`. Then `c_(0^m)=M`, all other multiplicities vanish, and

```text
E_m=M^2.                                                  (5.1)
```

All variables (3.1) lie in the all-zero Hamming orbit, (3.3) and every moment
matrix (3.4) are rank-one PSD, and (2.5) has zero on both sides because
`U_0=U_M=0^(m-1)`. For every `A*m>1`, (5.1) violates the desired bound. Thus
universal PSD plus exact overlap balance has no positive decay content.

### 5.2 Period `p`: overlap-only control cannot control energy

Fix any `p>=1`. Choose a primitive base-10 word of length `p`: for `p=1` use
`0`, and for `p>=2` use `0^(p-1)1` (it has exactly one `1`, so it cannot have
a smaller period). Repeat it and let `M=Kp`. For every `m>=p`, equality of two
length-`m` phase blocks would force the period word to be invariant under
their phase difference, contradicting primitivity. Thus the `p` phase blocks
are distinct and each occurs exactly `K=M/p` times. Therefore

```text
E_m=p*K^2=M^2/p.                                         (5.2)
```

Because `M` is a period multiple, `U_M=U_0`; hence every equation (2.5) is
exactly balanced with zero endpoint defect. All weighted moment matrices are
PSD. Whenever `A*m>p`, (5.2) violates the target. This proves that even exact
prefix/suffix flow balance, all Hamming symmetries, and bounded support do not
produce the needed logarithmic-depth decay.

### 5.3 Repeated de Bruijn: fixed-order moments cannot control growing depth

Fix a contiguous local order `r>=1`. A cyclic base-10 de Bruijn word `B_r` of period
`P=10^r` exists: take an Euler circuit in the directed graph whose vertices
are `(r-1)`-words and whose edges are `r`-words, from prefix to suffix. The
graph is balanced and strongly connected, so the circuit uses every `r`-word
once. Consequently every `ell<=r` word occurs exactly `10^(r-ell)` times per
period.

Repeat `B_r` and choose `M=KP`. For every tested contiguous local order
`ell<=r`, the all-start empirical `ell`-block law is exactly uniform, so every
moment or three-point statistic determined solely by those contiguous local
laws agrees with the uniform cyclic model. This does not cover arbitrary
noncontiguous coordinate probes. Endpoint balance is exact because
`U_M=U_0`.

For any audited depth `m>=r`, the first `r` digits identify the phase, so the
`P` phase `m`-blocks are distinct and each has multiplicity `K`. Hence

```text
E_m=P*K^2=M^2/10^r.                                      (5.3)
```

For every fixed contiguous order `r`, choosing `A*m>10^r` violates the target
despite perfect contiguous block statistics through order `r`, universal PSD
at every audited depth, and exact overlap balance. More generally, any
contiguous-order function `r(m)` with `10^r(m)=o(m)` fails by the same
construction. This is why bounded contiguous local moments cannot control
growing-depth collision energy.

The three proofs cover the requested boundaries separately: constant words
kill universal PSD; arbitrary primitive periods kill overlap-only control;
repeated de Bruijn periods kill bounded contiguous-local-order control even
when all lower contiguous block laws are exactly uniform. Finite replay
examples in `verify_t149.py` are only an
`experiment` corroborating these formulas.

## 6. Theorem-level nonduplication table

Comparator files are not mathematical premises. Literature statements in
their reports may be `literature-checked`, but local deductions remain
`proof sketch`; T144 is an unverified note. Byte-exact copies of every table
input are in `prior_evidence.tar.gz` (SHA-256
`1f1607b4accb32262c9decde945efab5a85d09391f988d4a8f5376ee1235df7a`).
The table records fingerprints and boundaries without promoting those
deductions.

| item | exact inspected artifact, SHA-256, locator | theorem-level boundary with T149 |
|---|---|---|
| T110 | `knowledge_library/t110/REPORT.md`, `4eaa088e...a3cb668`, Sections 6.1-6.2, lines 418-490 | fixed-order Gowers and metric higher correlations; T149 instead audits q-ary three-point PSD and gives a self-contained Gram/trace obstruction |
| T119 | `knowledge_library/t130/prior-t119-REPORT.md`, `72b10e92...3f23a`, Section 6, lines 422-625; recovered package incomplete | Toeplitz/Prony moment rank and atomic recovery; T149 uses Hamming Terwilliger blocks and rejects positivity without any rank inference |
| T121 | `knowledge_library/t121/REPORT.md`, `01b97953...6cf2`, Section 3, lines 115-158 | exact global Parseval collision L2; T149 does not rederive a Fourier expansion and tests three-point feasibility instead |
| T125 | `knowledge_library/t125/REPORT.md`, `1ce372d3...461a`, Section 3, lines 98-168 and Section 5, lines 278-345 | all-subset correlation expansion and fixed-order gap; T149's de Bruijn separator is a q-ary moment-hierarchy obstruction, not a correlation estimate |
| T132 | `knowledge_library/t132/REPORT.md`, `1d1aa950...23bd`, Section 3, lines 107-184 | weighted residue projection and majorization; T149 preserves multiplicities in Hamming triple orbits and does not project labels modulo q |
| T135 | `knowledge_library/t135/REPORT.md`, `4439850a...5e21`, Section 5.1-5.2, lines 194-306 | the note argues that Renyi-2 projection tensorization fails; T149 neither assumes tensorization nor imports that unverified deduction |
| T140 | `knowledge_library/t140/REPORT.md`, `ff05177c...f35c`, Sections 5-6, lines 301-489 | supersaturation/container census with growing-codegree obstruction; T149 is feasibility/energy, with no census claim |
| T144 | `knowledge_library/notes/t144/REPORT.md`, `96c68569...da7a`, Sections 1-3, lines 37-99, unverified `proof sketch` | the note argues a direct method-of-types census after residue splitting; T149 makes no bad-word count and does not use that note as a premise |
| active T147 | no readable T147 artifact in the refreshed snapshot; active lease only in `orchestrator-input.json`, SHA-256 `6fa45447...7d5`, lines 189-199 | theorem content unavailable, so no nonduplication claim is made against T147; T149's independent negative conclusion does not depend on it |

Full comparator hashes and archive members are checked by `verify_t149.py`.
The abbreviations above are display-only. The nearest branches are T119 (PSD
moments but Toeplitz/rank rather than Hamming triples), T125 (fixed-order
obstruction but correlation rather than Terwilliger feasibility), and T135
(overlapping three-coordinate collision laws but entropy tensorization rather
than SDP). No theorem candidate or counterfamily is copied from those notes.

## 7. Additional unproved pi-specific premises

These premises are stated separately and are not claimed.

**Toward T7.** For the actual base-10 orbit labels
`B_(i,m)(pi)=floor(10^m*{10^i*pi})`, one would need a strictly increasing
choice of prefixes with the exact canonical-style quantifiers and, for each
required `(A,m)`, an `N` satisfying

```text
max_b #{0<=i<N:B_(i,m)(pi)=b} <= N/(A*m).                (PI-ATOM)
```

Then (4.1) gives the ordered diagonal-inclusive cylinder energy bound used by
the T7 finite interface. `PI-ATOM` is unproved and stronger than the desired
energy estimate; neither retained source supplies it.

**Toward T107.** Three-point PSD would additionally need to imply, on one
increasing pi-prefix sequence and a positive-density triangular family of
levels, both T107's literal active-boundary budget and its row Fourier budget:

```text
rowBoundaryLoad(ell,N) <= N/(40*10^ell),
||rowFourierRemainder(ell,N)|| <= N^2/(10*10^ell).        (PI-ROW)
```

`PI-ROW` is unproved. S1-S4 contain neither the decimal boundary statistic nor
the fixed-pi Fourier remainder. Assuming it would supply the missing analytic
input rather than derive it from PSD.

## 8. Scoped verdict

**CLOSE:** nonbinary three-point/Terwilliger positivity, bounded contiguous
local moments, and exact prefix/suffix overlap consistency do not by themselves
control weighted collision energy at growing decimal depth. The
only surviving quantitative implication found is the direct atom cap (4.1),
whose histogram kill test simply asks for the missing anti-concentration and
is not furnished by either retained theorem. There is no bounded successor.

This closes only this applicability language. It does not refute the open
canonical question, T7's finite energy route, T107's conditional route, or a
future genuinely non-universal arithmetic theorem for the fixed pi orbit.
