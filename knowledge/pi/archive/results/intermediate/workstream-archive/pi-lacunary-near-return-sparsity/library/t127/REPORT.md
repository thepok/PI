# T127: bounded clean-restart cross-domain mechanism scout

Search date: 2026-08-10 UTC.

Primary-source statements are `literature-checked`. Coverage normalization,
parameter substitutions, and applicability deductions are `proof sketch`.
Replay output is an `experiment` checking only hashes, counts, archive
contents, and finite arithmetic.

```text
TOTAL_INSPECTED_PRIMARY_SOURCE_COUNT: 11
PRIMARY_SOURCE_CAP: 12
FINAL_CLEAN_SOURCE_COUNT: 3
FINAL_CLEAN_SEARCHED_DOMAIN_COUNT: 3
FINAL_PRESELECTION_ABSENT_CELL_COUNT: 3
DISCARDED_SOURCE_COUNT: 8
RETAINED_CANDIDATE_COUNT: 3
CANDIDATE_CAP: 4
SURVIVOR_COUNT: 0
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

The execution had two discarded source-first pilots and one gap check that
found a T105 duplicate. All eight associated sources remain charged to the
cap and pinned, but support no retained candidate. The final clean corpus is
S8, S9, and S11, selected only after the corresponding J-A, J-B, and J-D
freeze files existed. No fixed-pi, C1, or C2 conclusion is made.

## 1. Exact statement and ambiguities

Original source URL: none. The local question was formulated on 2026-07-22.
`canonical_statement.txt` is byte-exact, SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.

For integers `n,N>=1`,

\[
Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
\|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{1.1}
\]

Pairs are ordered, all diagonal pairs are included, and the cutoff is strict.
The canonical quantifiers are

\[
\forall A\ge1\ \exists n_0\ge1\ \forall n\ge n_0\
\exists N=N(A,n)\ge1:\quad AnQ_\pi(n,N)\le N^2.
\tag{1.2}
\]

Ambiguities fixed for this scout:

1. A paper counts once although `SOURCES.tar` contains both PDF and mechanical
   `pdftotext -layout` output.
2. All inspected papers count, including discarded pilots and the duplicate
   gap check. Only S8, S9, and S11 support final cards.
3. A cell is a subject plus a quantified observable, not shared terminology.
   Absence is only from frozen T89--T126.
4. A failed applicability test rejects only the displayed theorem as a
   certificate. It is not a necessity claim.
5. `proof sketch` notes remain unverified comparison memory.
6. T125 and T126 had active leases and no readable artifact; their collective
   active lanes are not assigned to individual IDs.
7. Every candidate is an A13/A14 related mechanism unless a separate transfer
   is proved.

## 2. T89--T126 coverage matrix

`PRIOR_EVIDENCE.tar` bundles reports, notes, Lean interfaces, rejected-report
blobs, and binding metadata. `LC/PS` means source quotations are
`literature-checked` while deductions are `proof sketch`; `MC` applies only to
the cited Lean declarations.

| Item | level/state | normalized fingerprint | disposition | archive evidence |
|---|---|---|---|---|
| T89 | LC/PS | exact decimal truncations collapse; automatic/Mahler constants have linear complexity and high collisions | hold | `knowledge_library/t89/REPORT.md` |
| T90 | LC/PS | constructed expanding-map points, discrepancy, Stoneham comparator | mixed | `knowledge_library/t90/REPORT.md` |
| T91 | note LC/PS | fixed substitutions lose all-start mass or multiplicity | mixed | `knowledge_library/notes/t91/REPORT.md` |
| T92 | MC discriminator, note PS | constant-run short-to-remote charging | local close | `knowledge_library/notes/t92/REPORT.md` |
| T93 | note LC/PS | fixed Stoneham skeleton plus tail | sibling | `knowledge_library/notes/t93/REPORT.md` |
| T94 | note PS/experiment | paperfolding tensor/carry profiles | model | `knowledge_library/notes/t94/REPORT.md` |
| T95 | note PS | overlap-period charging | later T100 | `knowledge_library/notes/t95/REPORT.md` |
| T96 | note LC/PS | maximal-order Stoneham repetition | sibling | `knowledge_library/notes/t96/REPORT.md` |
| T97 | note PS/experiment | exact paperfolding dyadic collisions | model | `knowledge_library/notes/t97/REPORT.md` |
| T98 | note PS | conditional charging/cover/irrationality Fejer interface | conditional | `knowledge_library/notes/t98/REPORT.md` |
| T99 | note LC/PS | exceptional-prime Stoneham | hold | `knowledge_library/notes/t99/REPORT.md` |
| T100 | MC | universal finite-word charging | formalizes T95 | `knowledge_library/t100/T100UniversalCharging.lean` |
| T101 | note LC/PS | paperfolding splitting mass only order `1/n` | close | `knowledge_library/notes/t101/REPORT.md` |
| T102 | note LC/PS | coprime Stoneham order/coset profile | develop model | `knowledge_library/notes/t102/REPORT.md` |
| T103 | LC/PS | Toeplitz periodic holes force collisions | close | `knowledge_library/t103/REPORT.md` |
| T104 | LC/PS | one-base Mahler radial behavior; restricted-denominator approximation; self-similar/model-measure Fourier decay; metric lacunary sums | hold | `knowledge_library/t104/REPORT.md`, Sections 2--8 |
| T105 | LC/PS | additive energy; complete multiplicative-subgroup sums including S10's exact theorem; decimal-difference modular sums | close | `knowledge_library/t105/REPORT.md`, Sections 2--7 |
| T106 | MC conditional | finite branching resonance trees | obstruction | `knowledge_library/t106/FiniteBranchingResonanceTree.lean` |
| T107 | MC conditional | triangular boundary/Fourier defect implies splitting | premise open | `knowledge_library/t107/T107AveragedTriangularFejer.lean` |
| T108 | MC conditional | charging plus irrationality/residual input bounds returns | inputs open | `knowledge_library/t108/T108LiteralTransport.lean` |
| T109 | rejected LC/PS | perturbation/shadowing/robustness certificates | terminal needs-review | `knowledge_library/t117/prior-t109-REPORT.md`; escalation |
| T110 | LC/PS | fixed-order Gowers and fixed-degree multiplicative sequences | hold | `knowledge_library/t110/REPORT.md` |
| T111 | LC/PS/experiment | de Bruijn remote-label separation | develop model | `knowledge_library/t111/REPORT.md` |
| T112 | LC/PS/experiment | carry local limits and cocycles | hold | `knowledge_library/t112/REPORT.md` |
| T113 | note LC/PS | effective point avoidance | hold | `knowledge_library/notes/t113/REPORT.md` |
| T114 | LC/PS | interpolation determinants miss height/rank/occupancy | close | `knowledge_library/t114/REPORT.md` |
| T115 | LC/PS/experiment | one explicit base-10 Riesz coefficient recursion and spike | close | `knowledge_library/t115/REPORT.md` |
| T116 | LC/PS/experiment | weighted avoidance tree | hold | `knowledge_library/t116/REPORT.md` |
| T117 | LC/PS/experiment | polynomial/Legendre trace-word sums | hold | `knowledge_library/t117/REPORT.md` |
| T118 | LC/PS/experiment | private cyclotomic order; short special-numerator geometric orbit unresolved | close | `knowledge_library/t118/REPORT.md` |
| T119 | rejected LC/PS | collision concentration versus predictive/Hankel/Prony rank | terminal needs-review | blob `.../sha256/77/773046...`; escalation |
| T120 | LC/PS/experiment | countable renewal laws lack one path/uniform depth | hold | `knowledge_library/t120/REPORT.md` |
| T121 | LC/PS/experiment | global Walsh/Parseval L2 and complete Legendre sums | develop model | `knowledge_library/t121/REPORT.md` |
| T122 | rejected LC/PS | discrepancy and vector balancing | terminal reject | blobs `.../97/974833...`, `.../6e/6ea3b7...`; escalation |
| T123 | parked LC/PS | full-shift specification; Thue--Morse `p(m)<=4m-2` and `E>=N^2/(4m-2)` | parked | blob `.../4e/4e3998...`; escalation |
| T124 | accepted note LC/PS | branching decimal monodromy lacks deterministic coding | hold | `knowledge_library/notes/t124/REPORT.md` |
| T125 | unavailable | one collective active lane; no individual fingerprint inferred | active | `orchestrator-input.json` |
| T126 | unavailable | one collective active lane; no individual fingerprint inferred | active | `orchestrator-input.json` |

Thus T109, T119, and T122 are terminal; T123 is parked; T125--T126 are
active and unavailable.

## 3. Checkable preselection chronology

The chronology is preserved rather than repaired in prose after the fact.

1. S1--S7 were source-first pilots. They are discarded and charged.
2. `PRESELECTION_FREEZE.md`, timestamp `2026-08-10T10:58:31Z`, froze J-A,
   J-B, and proposed J-C before S8--S10 selection and named no source.
3. S10 showed J-C duplicated T105. J-C and S10 were discarded.
4. `PRESELECTION_REPLACEMENT.md`, timestamp `2026-08-10T11:05:36Z`, froze
   J-D before S11 selection and named no source.
5. S11 was narrower than J-D, leaving J-D unfilled but providing a pinned
   negative adjacent theorem.

The final clean searched cells are exactly:

| cell | domain | pre-source absent observable | nearest covered boundary | state after source |
|---|---|---|---|---|
| J-A | Mahler/functional equations | lifting homogeneous algebraic relations among several Mahler values to functional relations | T89 individual automatic constants; T104 one-base scalar/radial behavior; T115 one explicit coefficient recursion | S8 exact, quantitatively inapplicable |
| J-B | symbolic entropy/collision | general subquadratic-complexity structural restriction without fixed substitution, automaton, or specification | T91/T94/T101 fixed substitutions; T123 specification and explicit Thue--Morse collision lower bound | S9 exact, quantitatively inapplicable |
| J-D | short structured exponential sums | pointwise power-saving reciprocal-phase sum over an arbitrary interval | T105 energy/complete subgroups; T117 polynomial trace words; T118 initial geometric orbit | S11 only initial interval/log saving; cell remains empty |

These are three absent cells across three requested domains. The failed J-C
gap check is not a retained cell or candidate.

## 4. Target thresholds

Bundled T7 has

\[
E_\pi(n,N)\le Q_\pi(n,N)\le3E_\pi(n,N),\qquad
\forall A\ \exists n_0\ \forall n\ge n_0\ \exists N:\ AnE_\pi(n,N)\le N^2.
\tag{4.1}
\]

Bundled T10's obstruction includes

\[
\left|\sum_{j=0}^{J-1}e(h(10^r-1)10^j\pi)\right|
>\frac{J}{131072A^2n^2},\quad1\le h\le256An,\quad J\ge K.
\tag{4.2}
\]

Bundled T28 requires adjacent `Q_i=10^{j_i}(10^{s_i}-1)` and

\[
Q_0e_1+UQ_1e_0<1.
\tag{4.3}
\]

Bundled T107 requires, for `q=10^ell`,

\[
B_{child}+\tfrac12B_{parent}\le\frac{P}{40q},\qquad
\|R_\ell(P)\|\le\frac{P^2}{10q}
\tag{4.4}
\]

on one coherent increasing prefix family.

## 5. C-LIFT: Mahler relation lifting

### Exact theorem and ranges

S8 is Boris Adamczewski and Colin Faverjon, *A New Proof of Nishioka's
Theorem in Mahler's Method*. Printed p. 1012, Theorem 2: fix integer `q>=2`;
let `f_1,...,f_m in Qbar[[z]]` be `M_q`-functions in one system

\[
\mathbf f(z)=A(z)\mathbf f(z^q),\qquad
A(z)\in GL_m(\overline{\mathbb Q}(z)).
\tag{5.1}
\]

Let algebraic `alpha` satisfy `0<|alpha|<1` and be regular, meaning every
`A(alpha^{q^k})`, `k>=0`, is defined and invertible. For every homogeneous
`P in Qbar[X_1,...,X_m]` with `P(f_1(alpha),...,f_m(alpha))=0`, there is
`Pbar in Qbar[z,X_1,...,X_m]`, homogeneous in `X`, such that

\[
\overline P(z,\mathbf f(z))=0,\qquad
\overline P(\alpha,X)=P(X).
\tag{5.2}
\]

The homogeneous qualification is literal; arbitrary affine relations would
require an additional homogenization argument.

### Substitution, distinction, and rejection test

The formal decimal-shaped substitution is `q=10`, `alpha=1/10`, and a common
system of several digit-related functions. No such regular system is supplied
for the prescribed orbit.

T89 concerns individual automatic/Mahler constants and collision-rich linear
complexity, not a relation ideal. T104 concerns scalar irrationality and
one-base radial behavior, not multivalue lifting. T115 concerns one explicit
coefficient/Riesz recursion, not algebraic value relations. Thus C-LIFT's
observable is distinct, though still a representation theorem.

Normalize T107's requirements as

\[
D_B=\frac{40q}{P}(B_{child}+\tfrac12B_{parent})\le1,
\qquad D_F=\frac{10q}{P^2}\|R_\ell(P)\|\le1.
\tag{5.3}
\]

S8 outputs a polynomial relation and contains no prefix `P`, level `ell`,
boundary count, Fourier remainder, or rate. It cannot certify (5.3).

Conjectural transfer premise `PI-LIFT`: exhibit a regular base-10 Mahler
system containing prescribed-orbit observables and prove a new quantitative
relation-to-defect theorem implying (5.3). Neither part is asserted. C-LIFT
is rejected; it is not a survivor.

## 6. C-SQ: subquadratic symbolic rigidity

### Exact theorem and ranges

S9 is Van Cyr and Bryna Kra, *The Automorphism Group of a Shift of
Subquadratic Growth*. ArXiv PDF p. 2, Theorem 1.1, with Definition 2.2 on p. 5:
let `X` be a two-sided subshift over a finite alphabet, topologically
transitive, and let `P_X(m)` count nonempty length-`m` cylinders. If

\[
\liminf_{m\to\infty}\frac{P_X(m)}{m^2}=0,
\tag{6.1}
\]

then, for `H=<sigma>`, the quotient `Aut(X)/H` is periodic. Equivalently each
automorphism has some positive power equal to a shift power.

### Substitution, distinction, and rejection test

The related-model substitution takes the two-sided orbit closure of a named
symbolic path and would first require topological transitivity and (6.1).
Neither is claimed for the prescribed decimal path.

T91/T94/T101 concern particular substitutions and paperfolding. T123 concerns
full-shift specification and explicitly derives
`E_TM(m,N)>=N^2/(4m-2)` from linear complexity. S9 instead quantifies every
topologically transitive subquadratic shift and concludes automorphism
rigidity; it supplies no occupancy estimate.

For all-start counts `c_u`, Cauchy gives only

\[
E(m,N)=\sum_uc_u^2\ge\frac{N^2}{P_X(m)}.
\tag{6.2}
\]

T7 needs an upper bound `AmE(m,N)<=N^2`. Neither (6.1) nor periodicity of the
automorphism quotient controls `max c_u` or reverses (6.2).

Conjectural transfer premise `PI-SQ`: prove the prescribed orbit closure meets
S9's hypotheses and add a new automorphism-to-occupancy theorem yielding the
T7 upper budget. This is not asserted. C-SQ is rejected; it is not a survivor.

## 7. C-RECIP: reciprocal-phase negative source

### Exact theorem and ranges

S11 is J. Bourgain and M. Z. Garaev, *Sumsets of Reciprocals in Prime Fields
and Multilinear Kloosterman Sums*. ArXiv v1 printed p. 10, Theorem 16: for a
large prime `p`, integer `1<N<p`, `n*` the inverse of `n mod p`, and uniformly
over `(a,p)=1`,

\[
\left|\sum_{n\le N}e_p(an^*)\right|
\ll N\frac{(\log\log p)^3\log p}{(\log N)^{3/2}},
\tag{7.1}
\]

with absolute implied constant. The source notes that for fixed
`N=p^epsilon` the relative saving is
`O((log log p)^3/(log p)^{1/2})`, and that (7.1) is nontrivial when

\[
N>\exp((\log p)^{2/3}(\log\log p)^3).
\tag{7.2}
\]

This is an initial interval and logarithmic saving. It does not fill frozen
J-D, which required arbitrary shifts and a fixed power saving.

### Substitution, distinction, and rejection test

T105's closest sums run over complete multiplicative subgroups or decimal
differences. T117 uses multiplicative characters of shifted polynomials over
the complete field. T118 preserves the ordered geometric orbit `10^j` at a
special numerator. S11 instead applies the inversion map to an additive
initial interval.

A literal T10 identification for three terms would require some nonzero `c`
and `x` with

\[
c(x+j)^{-1}\equiv\lambda10^j\pmod p,\qquad j=0,1,2.
\tag{7.3}
\]

Successive ratios force `x/(x+1)=10` and `(x+1)/(x+2)=10`, hence
`9x=-10` and `9x=-19`, so `p=3`; then one of three consecutive residues is
zero and an inverse is undefined. Thus no useful literal three-term map from
(7.1) to T10 exists. This rejects the substitution, not reciprocal-sum theory.

Conjectural transfer premise `PI-RECIP`: construct a nonliteral coding from
the adaptive geometric phases in (4.2) to reciprocal intervals, preserve
length and character uniformly, and prove the separate real-to-modular error
budget. No such premise is asserted. C-RECIP is a negative card and not a
survivor.

## 8. Discard and exclusion audit

S1--S7 are source-first pilots. S10 is the exact complete-subgroup theorem
already pinned by T105, so J-C was correctly discarded after its gap check.
All eight remain in `SOURCES.tar` and count toward eleven.

| forbidden prior fingerprint | controlling rows | final outcome |
|---|---|---|
| representation | T89/T104/T115 | C-LIFT distinct observable but rejected |
| Stoneham | T90/T93/T96/T99/T102 | not retained |
| invariant measure | T104 | not retained |
| finite state | T91/T94/T101 | C-SQ is general, then rejected |
| carry | T112 | not retained |
| additive energy | T105 | duplicate S10 discarded; C-RECIP distinct and rejected |
| determinant | T114 | not retained |
| avoidance | T113/T116 | not retained |
| renewal | T120 | not retained |
| global L2 | T121 | no upper-L2 survivor |
| vector balancing | terminal T122 | not retained |
| specification | parked T123 | explicitly distinguished from C-SQ |
| finite-field trace | T117 | explicitly distinguished from C-RECIP |
| active multiplicative-sequence lane | T125/T126 collective; T110 comparator | not retained |
| active hypergeometric-orbit lane | T125/T126 collective; T124 note | not retained |

## 9. Scoped verdict

**Verdict: close the final three-cell T127 clean scout.**

Mahler relation lifting supplies no finite defect rate; subquadratic symbolic
rigidity supplies no collision upper bound; and the best pinned reciprocal
sum is both narrower than J-D and incompatible with even a literal
three-term geometric orbit. There are zero survivors.

No successor is selected. This negative map records only the three final
pre-frozen cells and the discarded-source history. It establishes no
canonical-point estimate and no program conjecture.
