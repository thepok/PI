# T133: centered hypergeometric valuations do not enlarge the orbit range

Status: `proof sketch`. Source statements explicitly attributed in Section 2
are `literature-checked` against three pinned primary PDFs. All specializations,
valuation identities, automaton calculations, extrema, and orbit substitutions
are independently derived below. `verify_t133.py` supplies an `experiment` that
replays finite instances and integrity checks; finite evidence is not a proof.

Audit date: 2026-08-10 UTC.

```text
SEARCHED_DOMAIN_COUNT: 3
PRIMARY_SOURCE_COUNT: 3
CANDIDATE_CARD_COUNT: 3
RETAINED_CANDIDATE_COUNT: 1
PRE_KILL_SURVIVOR_COUNT: 1
POST_KILL_SURVIVOR_COUNT: 0
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

This is an A13/A14 related-model report. It makes no fixed-pi, C1, or C2
claim.

## 1. Canonical statement, scope, and ambiguities

The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
The canonical question fixes pi, base 10, the strict circle-distance cutoff
`10^(-n)`, ordered pairs, and all diagonal pairs. Its quantifiers are

```text
for every A >= 1, there exists n0 >= 1 such that
for every n >= n0, there exists N >= 1 with
A*n*Q_pi(n,N) <= N^2.
```

The following ambiguities are normalized before the scout.

1. The coefficient index `n`, the base-5 block length `r`, the denominator
   precision `m`, and decimal time `j` are distinct.
2. The cleared-product threshold modulo `5^m` is not the decimal-time
   transient of a reduced rational coefficient.
3. Occupancy means ordered, diagonal-inclusive equality occupancy in the named
   rational model. It is not metric near-return occupancy for pi.
4. `N asymp log q` uses the true reduced denominator `q`, not the unreduced
   hypergeometric denominator.
5. T126 is unverified motivation and a source map only. No deduction from its
   report is used as a premise.
6. Active T131--T132 are comparison availability boundaries: no mathematical
   artifacts for them are present in the binding snapshot.

## 2. Bounded three-domain scout

Exactly three domains were searched, with one primary source inspected in each
domain. Search stopped at three sources and three candidate cards. "Retained"
means surviving the initial relevance screen into the load-bearing calculation;
under that convention only C-H1 is retained.

| ID | Domain | Primary source and exact locator | Sourced fact used |
|---|---|---|---|
| S1 | hypergeometric arithmetic | Sandip Singh and T. N. Venkataramana, "Arithmeticity of Certain Symplectic Hypergeometric Groups," arXiv:1208.6460v2, <https://arxiv.org/abs/1208.6460>, PDF p. 1, displayed operator in the paragraph beginning `Set theta` | For tuples `alpha,beta`, the source defines `theta=z d/dz` and `D=prod_i(theta+beta_i-1)-z prod_i(theta+alpha_i)`. |
| S2 | automatic or regular sequences | Boris Adamczewski, Jason Bell, and Daniel Smertnig, "A Height Gap Theorem for Coefficients of Mahler Functions," arXiv:2003.03429v2, DOI 10.4171/JEMS/1244, <https://arxiv.org/abs/2003.03429>, printed pp. 8--9, Definition 3.3, Definition 3.4, Theorem 3.5; printed p. 9, paragraph before Definition 3.6 | The source defines the `k`-kernel and linear representation, states their characterization of `k`-regular sequences, and records that regular power series are Mahler. |
| S3 | Mahler functional equations | Dzmitry Badziahin and Evgeniy Zorin, "On the Irrationality Measure of the Thue--Morse Constant," arXiv:1707.06677v1, DOI 10.1017/S0305004118000117, <https://arxiv.org/abs/1707.06677v1>, PDF pp. 2--3, equations (2)--(5) | The source defines a Mahler function, gives `t_(2n)=t_n`, `t_(2n+1)=1-t_n`, and gives the product and exact equation `f_TM(z^2)=z/(z-1) f_TM(z)`. |

The PDFs, URLs, hashes, and extraction anchors are itemized in
`SOURCE_PINS.md`. Restricted-denominator approximation and structured
exponential sums were not searched.

### Candidate cards

| Candidate | Normalized fingerprint | Decision before the quantitative kill |
|---|---|---|
| C-H1 | The S1 hypergeometric operator is specialized independently; its cleared coefficient product has a three-state weighted base-5 transducer computing the centered 5-valuation. | Sole survivor. It has the exact requested valuation, extremal, denominator, transient, order, and occupancy interfaces. |
| C-REG | S2's regular-sequence interface supplies the correct language for a finite linear representation, but no inspected source states the H1 valuation automaton. | Screened: structural template only. The H1 automaton must be derived, not imported. |
| C-TM | S3 supplies an exact automatic recurrence and Mahler equation for Thue--Morse. | Screened: it has no hypergeometric valuation or reduced-modulus arithmetic and duplicates the symbolic/Mahler branch represented by T91/T94/T115. |

Thus only C-H1 reaches the load-bearing calculation. There is no claim that
the automaton below appears in S1--S3.

## 3. Independent H1 reconstruction

In S1's operator set

```text
alpha = (1/6,5/6), beta = (1,1).
```

This gives, by direct substitution rather than a quoted source theorem,

\[
  \mathcal L=\theta^2-z(\theta+1/6)(\theta+5/6).             \tag{3.1}
\]

For `F(z)=sum_(n>=0) a_n z^n`, `a_0=1`, coefficient comparison in
`mathcal L F=0` gives for `n>=1`

\[
  36n^2a_n=(6n-5)(6n-1)a_{n-1}.                            \tag{3.2}
\]

Iteration gives the named H1 coefficient model

\[
 a_n={U_n\over36^n(n!)^2},\qquad
 \boxed{U_n=\prod_{k=1}^n(6k-5)(6k-1)},\quad U_0=1.        \tag{3.3}
\]

The factors are exactly the positive integers at most `6n` coprime to 6.
Inclusion-exclusion on products therefore gives the independently derived
identity

\[
 \boxed{U_n={(6n)!\,n!\over12^n(3n)!(2n)!}.}               \tag{3.4}
\]

For every prime `p>=5`, Legendre's floor formula applied to (3.4) gives

\[
 \boxed{v_p(U_n)=\sum_{a\ge1}\left(
 \left\lfloor{6n\over p^a}\right\rfloor-
 \left\lfloor{3n\over p^a}\right\rfloor-
 \left\lfloor{2n\over p^a}\right\rfloor+
 \left\lfloor{n\over p^a}\right\rfloor\right).}          \tag{3.5}
\]

The sum is finite. Also `v_2(U_n)=v_3(U_n)=0` directly from the product.

Let `s_5(t)` be the sum of the base-5 digits of `t`. Legendre's identity
`v_5(t!)=(t-s_5(t))/4` in (3.4) gives the load-bearing identity

\[
 \boxed{v_5(U_n)-{n\over2}=
 {s_5(2n)+s_5(3n)-s_5(6n)-s_5(n)\over4}.}                 \tag{3.6}
\]

Equivalently define the integer sequence

\[
 \boxed{E(n)=2v_5(U_n)-n=
 {s_5(2n)+s_5(3n)-s_5(6n)-s_5(n)\over2}.}                 \tag{3.7}
\]

No T126 formula is a premise of (3.1)--(3.7).

## 4. Complete weighted base-5 transducer

Read exactly `r` base-5 digits of `n` from least significant to most
significant, padding with high zeroes, where `0<=n<5^r`. Start in state `A`.
An entry `Q/e` means move to `Q` and add integer weight `e`. After the `r`
input digits, add the displayed terminal weight.

| state | digit 0 | digit 1 | digit 2 | digit 3 | digit 4 | terminal |
|---|---|---|---|---|---|---|
| A | A / 0 | X / 1 | X / 0 | X / -1 | X / -2 | 0 |
| X | A / 0 | X / 1 | X / 0 | X / -1 | F / 0 | 0 |
| F | X / 2 | X / 1 | X / 0 | X / -1 | F / 0 | 2 |

These are all 15 transitions. Their accumulated weight plus terminal weight is
exactly `E(n)`.

Here is a derivation rather than a table guess. During ordinary base-5
multiplication of `n` by `c in {2,3,6}`, let `kappa_c` be the incoming carry.
On digit `d`, the next carry is

\[
 \kappa'_c=\left\lfloor{cd+\kappa_c\over5}\right\rfloor.  \tag{4.1}
\]

The six reachable carry triples `(kappa_2,kappa_3,kappa_6)` collapse into
three weighted residual classes:

\[
\begin{split}
 A&=\{(0,0,0)\},\\
 X&=\{(0,0,1),(0,1,2),(1,1,3),(1,2,4)\},\\
 F&=\{(1,2,5)\}.
\end{split}                                                \tag{4.2}
\]

For each digit the contribution is

\[
 -d+2(\kappa'_6-\kappa'_3-\kappa'_2).                     \tag{4.3}
\]

Substitution of every triple in (4.2) and every `d=0,...,4` gives the table;
all four triples in `X` have the same weighted residual transition. The only
nonzero carry-flush contribution is 2 from `F`, giving its terminal weight.
This proves the output identity by the standard digit-sum/carry telescoping
formula

\[
 s_5(cn)=c s_5(n)-4\sum_{i\ge1}\kappa_{c,i}.               \tag{4.4}
\]

The device is minimal as a deterministic weighted-residual transducer: `F`
is distinguished by terminal value 2, and one-digit continuation `4`
distinguishes `A` from `X` (outputs `-2` and `2`, respectively, including the
terminal contribution).

This explicit representation is the required digit transducer. S2 supplies
the adjacent regular-sequence terminology, but no 5-regularity theorem is
needed here. For a direct arithmetic formulation, define
`Phi(q,0)=terminal(q)` and

\[
 \Phi(q,k+1;d+5m)=w(q,d)+\Phi(T(q,d),k;m).                 \tag{4.5}
\]

Then `E(n)=Phi(A,r;n)` for every `0<=n<5^r`. Equation (4.5) is also an exact
finite Mahler-type decimation recursion for the block polynomials; no
functional equation is needed in the later arithmetic.

## 5. Exact extremal envelope

Let `L_k(q)` and `H_k(q)` be the minimum and maximum continuation values from
state `q` with `k` digits remaining, including the terminal weight. Dynamic
programming on the complete transition table gives:

| remaining digits | A `(L,H)` | X `(L,H)` | F `(L,H)` |
|---|---|---|---|
| `k=0` | `(0,0)` | `(0,0)` | `(2,2)` |
| `k=1` | `(-2,1)` | `(-1,2)` | `(-1,2)` |
| `k=2` | `(-3,3)` | `(-2,3)` | `(-2,4)` |
| `k>=3` | `(-(k+1),k+1)` | `(-k,k+1)` | `(-k,k+2)` |

This table is an induction proof: the `k=0,1,2` base rows are direct
substitution, and for each subsequent row

\[
 L_{k+1}(q)=\min_{0\le d<5}(w(q,d)+L_k(T(q,d))),\quad
 H_{k+1}(q)=\max_{0\le d<5}(w(q,d)+H_k(T(q,d))).            \tag{5.1}
\]

Substituting the displayed formulas for any `k>=2` into all 15 transitions
reproduces the row for `k+1`. Starting at `A` proves

\[
 \boxed{\min_{0\le n<5^r}E(n)=-(r+1)\quad(r\ge1),}         \tag{5.2}
\]

and

\[
 \boxed{\max_{0\le n<5^r}E(n)=
 \begin{cases}1,&r=1,\\r+1,&r\ge2.\end{cases}}            \tag{5.3}
\]

For `r=0`, both extrema are zero. Witnesses are the base-5 words
`33...34` for the minimum, `1` for the `r=1` maximum, and, for `r>=2`,
`41...11` for the maximum; words are written most significant digit first.
Therefore

\[
 \boxed{\min_{0\le n<5^r}\left(v_5(U_n)-{n\over2}\right)
 =-{r+1\over2}\quad(r\ge1),}                              \tag{5.4}
\]

\[
 \boxed{\max_{0\le n<5^r}\left(v_5(U_n)-{n\over2}\right)
 =\begin{cases}1/2,&r=1,\\(r+1)/2,&r\ge2.\end{cases}}     \tag{5.5}
\]

These exact extrema replace T126's coarse logarithmic bounds; T126 remains
comparison memory only.

## 6. Power-of-5 threshold and complete reduction

For the cleared product define its 5-primary threshold

\[
 \tau_m=\min\{n\ge0:v_5(U_n)\ge m\}\quad(m\ge1).           \tag{6.1}
\]

The transducer computes `tau_m` exactly. Constant-explicitly, put
`R_m=ceil(log_5(4m+4))`. From (5.2)--(5.3), applied inside the block
`0<=n<5^(R_m)`, one obtains

\[
 \boxed{2m-R_m-1\le\tau_m\le2m+R_m+1.}                    \tag{6.2}
\]

Indeed `n*=2m+R_m+1<5^(R_m)` and its lower envelope is at least `m`; applying
the upper envelope to the first crossing gives the lower bound. This is a
power-of-5 threshold for the cleared numerator, not decimal time.

Now write `a_n=P_n/q_n` in lowest terms. From (3.3),

\[
 v_p(q_n)=\max(2n v_p(6)+2v_p(n!)-v_p(U_n),0).             \tag{6.3}
\]

For `p>=5`, subtracting `2v_p(n!)` from (3.5) leaves terms

\[
 \lfloor6x\rfloor-\lfloor3x\rfloor-\lfloor2x\rfloor-
 \lfloor x\rfloor\ge0,                                   \tag{6.4}
\]

by floor superadditivity with `6x=3x+2x+x`. Thus every denominator prime
`p>=5`, including 5, cancels. Since `U_n` is coprime to 6, Legendre's formula
for 2 and 3 gives

\[
 \boxed{q_n=2^{\alpha_n}3^{\beta_n},\quad
 \alpha_n=4n-2s_2(n),\quad\beta_n=3n-s_3(n).}             \tag{6.5}
\]

The centered 5-valuation controls only

\[
 v_5(P_n)=v_5(U_n)-2v_5(n!)={E(n)+s_5(n)\over2},           \tag{6.6}
\]

which does not alter the reduced modulus.

## 7. Decimal transient, order, orbit, and occupancy

At decimal time `j`, exact reduction gives

\[
 \boxed{\operatorname{den}(10^j a_n)=
 2^{\max(\alpha_n-j,0)}3^{\beta_n}.}                      \tag{7.1}
\]

Therefore the true decimal-time transient is exactly `alpha_n`, independent
of (5.4)--(5.5). After it,

\[
 10^{\alpha_n+s}a_n\equiv
 {P_n5^{\alpha_n}10^s\over3^{\beta_n}}\pmod1.             \tag{7.2}
\]

The numerator is a unit modulo 3. The elementary LTE identity

\[
 v_3(10^h-1)=2+v_3(h)\quad(h\ge1)                         \tag{7.3}
\]

therefore gives the exact tail order

\[
 \boxed{d_n=\operatorname{ord}_{3^{\beta_n}}(10)=
 \begin{cases}1,&\beta_n\le2,\\3^{\beta_n-2},&\beta_n\ge3.
 \end{cases}}                                             \tag{7.4}
\]

For a prefix of `N` decimal times, put `L=max(N-alpha_n,0)` and write
`L=u d_n+v`, `0<=v<d_n`. Every transient point is a singleton disjoint from
the tail, because equality at `i<j` is equivalent to

\[
 i\ge\alpha_n\quad\hbox{and}\quad d_n\mid(j-i).           \tag{7.5}
\]

Hence the complete ordered, diagonal-inclusive equality count is

\[
 \boxed{C_n(N)=
 \begin{cases}
 N,&N\le\alpha_n,\\
 \alpha_n+v(u+1)^2+(d_n-v)u^2,&N>\alpha_n.
 \end{cases}}                                             \tag{7.6}
\]

This substitutes the exact valuation envelope through every requested layer:
it sharpens (6.1)--(6.2), disappears from (6.5), leaves (7.1) unchanged, and
therefore leaves (7.4)--(7.6) unchanged.

## 8. Displayed logarithmic-range kill test

Fix integers `A>=1` and `n>=max(A,2)`. Take tail length `An` and full prefix

\[
 N=\alpha_n+An.                                           \tag{8.1}
\]

Since `beta_n>=2n`,

\[
 d_n\ge9^{n-1}\ge n^2\ge An.                             \tag{8.2}
\]

Thus (7.5) shows all first `N` model values are distinct, so

\[
 C_n(N)=N,\qquad A n C_n(N)=AnN\le N^2.                  \tag{8.3}
\]

But this remains exactly logarithmic in the true modulus. The elementary
bounds `2n<=alpha_n<=4n`, `2n<=beta_n<=3n` give

\[
 2n\log6\le\log q_n\le n(4\log2+3\log3)                 \tag{8.4}
\]

and

\[
 (A+2)n\le N\le(A+4)n.                                   \tag{8.5}
\]

Combining them displays the quantitative kill test:

\[
 \boxed{
 {A+2\over4\log2+3\log3}\log q_n
 \le N\le
 {A+4\over2\log6}\log q_n,
 \quad\text{so }N\asymp_A\log q_n.}                     \tag{8.6}
\]

Exact extrema for `v_5(U_n)-n/2` cannot change (8.6), because 5 is absent
from `q_n`. Therefore C-H1 fails the mandated range test despite its exact
finite-state arithmetic.

## 9. Named prior and active fingerprints

Every cited prior file is byte-pinned in `prior_evidence.tar.gz` and indexed in
`PRIOR_INDEX.md`. Notes are unverified comparison memory and are never treated
as discharged premises.

| Item and level | Normalized fingerprint | T133 boundary |
|---|---|---|
| T91, unverified `proof sketch`; source attributions labeled `literature-checked`; replay `experiment` | Thue--Morse, period-doubling, and paperfolding symbolic collision models. | T133 reads base-5 arithmetic digits and outputs a valuation. C-TM is rejected as symbolic duplication; C-H1 does not import a symbolic collision conclusion. |
| T94, unverified `proof sketch`; replay `experiment` | Paperfolding DFAO, carry/comparison tensor, and exact factor-collision decimation. | Its carries compare starts and factors in base 2. T133's six multiplication-carry triples compute one scalar valuation; no factor-pair automaton is reused. |
| T97, unverified `proof sketch`; replay `experiment` | Exact extremal envelope for a paperfolding collision recurrence on dyadic blocks. | Only the proof shape is analogous. The statistic and radix differ, and T133 derives its extrema from its own 15 transitions. |
| T101, unverified `proof sketch`; replay `experiment` | Paperfolding full-prefix energy gives a successor-splitting obstruction. | T133 makes no splitting inference from finite state; this is the explicit non-duplication boundary. |
| T112, source claims labeled `literature-checked`, deductions `proof sketch`, replay `experiment` | Carry local limits and finite transducers average random inputs or signed models and miss the prescribed pi path. | T133 is deterministic arithmetic, not a stationary carry law. It supplies no pi path. |
| T115, source claims labeled `literature-checked`, deductions `proof sketch`, replay `experiment` | A length-10 generalized Thue--Morse Riesz/Mahler recursion has persistent decimal-ray Fourier spikes. | C-TM is closed as this symbolic/Mahler kind; C-H1 has no Fourier cancellation claim. |
| T118, source claims labeled `literature-checked`, deductions `proof sketch`, replay `experiment` | Private prime powers give exact order, but useful pointwise bounds remain beyond logarithmic length. | T133 confirms the same scale obstruction for a different modulus: valuation sharpening leaves `N asymp log q`. |
| T124, unverified `proof sketch`; source quotations labeled `literature-checked`; replay `experiment` | H1 branching monodromy/expansion and the proposed cleared coefficient `U_n`. | Source-map motivation only. T133 independently reconstructs `U_n` and studies the deterministic coefficient path, not the branching word walk. |
| T126, unverified `proof sketch`; one source definition labeled `literature-checked`; replay `experiment` | Coarse valuation bounds, full denominator reduction, exact transient/order/occupancy, and an `O(log q)` H1 equality prefix. | Maximum overlap. T133's new related-model content is the explicit minimal transducer and exact extrema; the complete substitution shows that this refinement cannot alter T126's recorded barrier. |
| active T131 | The binding prompt calls it active, but no report, source pin, result, title, or fingerprint is present in the supplied snapshot. | Availability boundary only; no content or novelty claim is inferred. |
| active T132 | The binding prompt calls it active, but no report, source pin, result, title, or fingerprint is present in the supplied snapshot. | Availability boundary only; no content or novelty claim is inferred. |

The machine-checked T7 interface is the ordered, diagonal-inclusive finite
decimal-cylinder energy frontier (`T7-FiniteCylinderEnergy.lean`, lines
292--318 and 346--386). The machine-checked T107 interface is a triangular
Fejer criterion with separate boundary and Fourier budgets
(`T107-AveragedTriangularFejer.lean`, lines 31--69 and 150--199). Neither
interface supplies the arithmetic continuation absent here.

## 10. Separately stated unproved pi-transfer premise

`PI-H1-CONT-T133` (`conjecture`; **unproved additional arithmetic-continuation
premise**): for every integer `A>=1` and all sufficiently large `n`, with
`N=alpha_n+An`, every canonical fixed-pi near-return pair in `[0,N)^2`
satisfies

\[
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}
 \quad\Longrightarrow\quad
 10^i a_n\equiv10^j a_n\pmod1.                            \tag{10.1}
\]

This would continue the H1 arithmetic into the named T7 fixed-pi
finite-cylinder frontier while preserving ordered pairs and diagonals. It is
not asserted. No inspected source relates `a_n` to pi, controls the required
decimal errors or carries, or proves (10.1).

Moreover (10.1) has the same substantive burden as T126's unproved
`PI-H1-COLL` injection. Renaming that injection is expressly disallowed by the
kill test. It also does not supply T107's independent boundary and Fourier
budgets. Thus the only conceivable transfer is rejected rather than counted
as new input.

## 11. Replay and claim boundary

From a directory containing only the delivered files, run

```bash
python3 verify_t133.py
sha256sum -c SHA256SUMS
```

The verifier checks local hashes, PDF anchors, archive membership and member
hashes, all transitions from the six carry triples, valuation identities,
exact dynamic-programming extrema, displayed witnesses, reduced denominators,
5-primary thresholds, orders, occupancies, and logarithmic substitutions.
These bounded checks are an `experiment`; the universal arguments are the
displayed derivations.

No successor is proposed.

## 12. Scoped verdict

SCOPED_VERDICT: CLOSE
