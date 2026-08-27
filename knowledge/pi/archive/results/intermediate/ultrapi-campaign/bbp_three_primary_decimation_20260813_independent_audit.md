# Independent audit: BBP three-primary decimation

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is Marcel's immutable local question and has no external source
URL; none is invented here.

Audited frozen artifacts:

- [bbp_three_primary_decimation_20260813.md](bbp_three_primary_decimation_20260813.md),
  SHA-256
  `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0`;
- [bbp_three_primary_decimation_20260813_check.py](bbp_three_primary_decimation_20260813_check.py),
  SHA-256
  `abda4aa38bc575439320ecc60a44d0df8418be042b2bb0558f70f05c1c2dfc71`;
- [T74T74ThreePrimaryDecimation.lean](../../TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean),
  SHA-256
  `eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727`;
- imported [T73T73ThreePrimaryOrbit.lean](../../TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean),
  SHA-256
  `1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009`.

Independent checker:
[bbp_three_primary_decimation_20260813_independent_check.py](bbp_three_primary_decimation_20260813_independent_check.py),
SHA-256
`1304e1e4cb70c0bfba65b40cf32f7c282d447af3461398e305893e26e7f4f0ec`.
It imports no primary checker code.

## Verdict and exact qualification

**Independent audit verdict: PASS WITH NECESSARY NONFATAL BOUNDARY
QUALIFICATION.** The four term identities, exact LTE valuations, all-depth
finite-sum decimation, endpoint relations, both endpoint-unit nestings,
fixed-exponent inverse maps, and real-shadow bound survive independent
derivation.

The qualification is confined to the prose in Section 4 and the outcome
summary of the frozen primary report:

- every pre-drop grid at even $e\ge4$ is a nine-to-one refinement of its
  predecessor;
- the first drop transition $e=4\to2$ is **three-to-one**, from period
  $3$ to the trivial period $1$;
- every drop transition at even $e\ge6$ is nine-to-one, since its periods
  are $3^{e-3}$ and $3^{e-5}$.

Thus “the same argument applies to the drop grids” needs the explicit
$e=4$ exception. The formula $3^{e-5}$ is not an integer-period formula
at $e=4$. This does not affect decimation (10), nesting (19), fixed-$n$
compatibility, or any asymptotic claim. The primary artifacts were kept
frozen as requested.

The all-depth mathematical argument has status `proof sketch`; bounded
replays have status `experiment`; the dated source check has status
`literature-checked`; exactly the twelve stated T74 algebraic lemmas are
`machine-checked`. No joint CRT control or decimal target hitting follows.
Canonical V1 remains a `conjecture`.

## 1. Independent four-pole derivation

Write

\[
 f_i(k)=\frac{c_i}{(a_i k+b_i)16^k},
\quad
(a_i,b_i,c_i)=(8,1,4),(2,1,-1/2),(8,5,-1),(4,3,-1/2).
                                                               \tag{A1}
\]

Direct common-denominator expansion gives

\[
 \sum_i f_i(k)=
 \frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)16^k}.              \tag{A2}
\]

For the four offsets and multipliers

\[
             d=(1,4,5,6),\qquad m=(1,4,1,2),                 \tag{A3}
\]

ordinary integer expansion independently gives

\[
 a_i(9r+d_i)+b_i=9(a_i r+b_i),\qquad
 8r+d_i=m_i(a_i r+b_i).                                     \tag{A4}
\]

Substitution into (A1), including the geometric exponent
$9r+d_i=r+(8r+d_i)$, gives exactly

\[
 9f_i(9r+d_i)-f_i(r)
 =f_i(r)\bigl(16^{-(8r+d_i)}-1\bigr).                       \tag{A5}
\]

There is no cross-pole cancellation in this identity and no omitted factor
of 9 or 16.

## 2. Valuations and finite-sum decimation

For $q\ge1$, LTE applies because $3\mid16-1$ and $3\nmid16$:

\[
                    v_3(16^q-1)=v_3(15)+v_3(q)=1+v_3(q).
                                                                    \tag{A6}
\]

In (A5), $q=8r+d_i=m_i(a_i r+b_i)$, and every $m_i,c_i,16$
is a 3-adic unit. Consequently

\[
       v_3(f_i(r))=-v_3(a_i r+b_i),\qquad
       v_3(16^{-q}-1)=1+v_3(a_i r+b_i),
\]

so the difference in (A5) has the **exact** valuation

\[
                    v_3(9f_i(9r+d_i)-f_i(r))=1.             \tag{A7}
\]

Since every $a_i$ is invertible modulo 9, $a_i k+b_i\equiv0\pmod9$
has one residue class. Solving it gives exactly $k\equiv d_i\pmod9$.
For every other $k$, $v_3(a_i k+b_i)\le1$, hence

\[
                              9f_i(k)\in3\mathbb Z_{(3)}.   \tag{A8}
\]

Now take $F_i(q)=0$ for $q<0$ and
$F_i(q)=\sum_{r=0}^q f_i(r)$ for $q\ge0$. Partition the finite set
$0\le k\le M$ into the four lifted residue classes and their complements.
For pole $i$, the lifted indices are precisely

\[
 k=9r+d_i,\qquad
 0\le r\le\left\lfloor\frac{M-d_i}{9}\right\rfloor.       \tag{A9}
\]

Pairing those terms by (A5) and using (A8) on all remaining terms proves

\[
 9B_M-\sum_{i=1}^4F_i\!\left(
       \left\lfloor\frac{M-d_i}{9}\right\rfloor\right)
 \in3\mathbb Z_{(3)}                                       \tag{A10}
\]

for every $M\ge0$. This also verifies the negative-cutoff convention:
the cutoff vectors for $M=0,1,4,5,6$ are respectively

\[
(-1,-1,-1,-1),(0,-1,-1,-1),(0,0,-1,-1),
(0,0,0,-1),(0,0,0,0).                                     \tag{A11}
\]

Thus there is no hidden $r=-1$ term at the initial boundary.

## 3. Endpoint cutoffs and unit nesting

For even $e\ge2$, let

\[
 A_e=\frac{3^e-1}{8},\qquad M_e^-=5A_e-1,qquad M_e^+=5A_e.
                                                                  \tag{A12}
\]

Since $A_e=9A_{e-2}+1$, for every even $e\ge4$,

\[
 M_e^-=9M_{e-2}^-+13,qquad M_e^+=9M_{e-2}^++5.             \tag{A13}
\]

Substitution of $d=(1,4,5,6)$, with integer floor rather than formal
pattern matching, gives the exact cutoff vectors

\[
\begin{aligned}
M_e^- &: (M_{e-2}^-+1,M_{e-2}^-+1,M_{e-2}^-,M_{e-2}^-),\\
M_e^+ &: (M_{e-2}^+,M_{e-2}^+,M_{e-2}^+,M_{e-2}^+-1).
\end{aligned}                                                \tag{A14}
\]

At the pre-drop endpoint the two extra indices are
$M_{e-2}^-+1=M_{e-2}^+$. Their first and second linear denominators are

\[
 8M_{e-2}^++1=5\cdot3^{e-2}-4\equiv2\pmod3,
 \quad2M_{e-2}^++1=\frac{5\cdot3^{e-2}-1}{4}\equiv2\pmod3. \tag{A15}
\]

Also
$4M_{e-2}^++3=(5\cdot3^{e-2}+1)/2\equiv2\pmod3$.
Thus all extra or missing terms in (A14) lie in
$\mathbb Z_{(3)}$.

Using (A10) yields

\[
 9B_{M_e^-}-B_{M_{e-2}^-}\in\mathbb Z_{(3)},\qquad
 9B_{M_e^+}-B_{M_{e-2}^+}\in\mathbb Z_{(3)}.               \tag{A16}
\]

Together with the frozen epoch valuations, normalize

\[
 U_e^-=3^eB_{M_e^-},\qquad U_e^+=3^{e-1}B_{M_e^+}.          \tag{A17}
\]

Multiplying (A16) by $3^{e-2}$ and $3^{e-3}$, respectively, gives

\[
 U_e^-\equiv U_{e-2}^-\pmod{3^{e-2}\mathbb Z_{(3)}},
 \quad
 U_e^+\equiv U_{e-2}^+\pmod{3^{e-3}\mathbb Z_{(3)}}.       \tag{A18}
\]

Both are Cauchy sequences of 3-adic units. Independent localized modular
summation reproduced all six residue rows in the primary table, including
the edge cases $e=2$ and $e=4$.

## 4. Fixed-exponent inverse maps and the boundary correction

Let $g_n=(10^n-16)/3$. At pre-drop epoch $e$, the numerator and
denominator are reduced modulo $3^{e-1}$. From (A18), for every fixed
$n\ge1$,

\[
 U_e^-g_n\equiv U_{e-2}^-g_n\pmod{3^{e-3}}.                 \tag{A19}
\]

Equivalently, if $x_{e,n}^-$ is represented at denominator
$3^{e-1}$,

\[
                         9x_{e,n}^-\equiv x_{e-2,n}^-\pmod1. \tag{A20}
\]

The periods are $3^{e-2}$ and $3^{e-4}$, so every old grid point has
exactly nine preimages for every even $e\ge4$.

For the drop grid, the analogous numerator moduli are $3^{e-2}$ and,
when nontrivial, $3^{e-4}$. Fixed-$n$ compatibility still follows from
the second congruence in (A18). The period statement, however, splits:

\[
\begin{array}{c|c|c|c}
\text{transition}&\text{new period}&\text{old period}&\text{fibre size}\\ \hline
e=4\to2&3&1&3\\
e\to e-2,\ e\ge6&3^{e-3}&3^{e-5}&9.
\end{array}                                                  \tag{A21}
\]

This is the necessary boundary qualification. The first drop transition is
not ninefold. Thereafter it is exactly ninefold. The independent checker
enumerates both cases rather than inferring fibre size from a formal ratio.

## 5. Uniform real shadow

Write $a(k)$ for the coefficient in (A2) before its factor $16^{-k}$.
It is positive, and for every $k\ge1$,

\[
 (2k+1)(4k+3)(8k+1)(8k+5)
 -k^2(120k^2+151k+47)
 =392k^4+873k^3+665k^2+194k+15>0.             \tag{A22}
\]

Thus $0<a(k)\le k^{-2}$. Summing the geometric tail gives

\[
 0<\pi-B_M
 =\sum_{k=M+1}^\infty\frac{a(k)}{16^k}
 \le\frac{16^{-M}}{15(M+1)^2}.                              \tag{A23}
\]

For pre-drop $M=M_e^-$, put $T=3^{e-2}$. Direct substitution gives

\[
 M=\frac{45T-13}{8}\ge5(T-1).                              \tag{A24}
\]

Because $(8/5)^5>10$, (A24) also implies
$\lfloor\log_{10}(16^M)\rfloor\ge M+T-1$. Hence all the
exponents below lie in the exact proportional BBP row.

For $M\le n<M+T$, using the slightly weaker $10^n\le10^{M+T}$,

\[
 |(10^n-16)(\pi-B_M)|
 \le\frac{10^{M+T}16^{-M}}{15(M+1)^2}.                     \tag{A25}
\]

The endpoint margin implies

\[
 10^{M+T}16^{-M}
 =(5/8)^M10^T
 \le(8/5)^5\left(\frac{31250}{32768}\right)^T.             \tag{A26}
\]

The ratio $31250/32768<1$, proving the claimed uniform exponential
shadow. This transfers approximation from the full rational BBP phase to
the actual pi-orbit segment, but it says nothing about where either phase
lies on the circle.

## 6. Formal audit

T74 was compiled independently with:

```bash
lake env lean --trust=0 \
  TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean
```

The result was `PASS`. Parsing the namespace found exactly twelve theorem
declarations: four affine folds, four exponent folds, and four rational
decimation identities. Parsing [audit/AxiomAudit.lean](../../audit/AxiomAudit.lean)
found exactly the same twelve fully qualified declarations and one T74
import. There were no additional or missing T74 declarations. The complete
central audit file was also compiled with `--trust=0` and exited successfully;
its T74 lines reported the same dependencies.

The exact reported axiom union was

```text
propext, Classical.choice, Quot.sound
```

The two reflexive exponent folds use no axioms. A source scan found no
`sorry`, `admit`, new `axiom`, `native_decide`, `opaque`, or `unsafe`
declaration in T74. No verification gate or allowlist was changed. The
machine-checked boundary is narrow: T74 does not formalize LTE, (A10), the
epoch valuations, endpoint nesting, grid refinement, the real tail, or V1.

## 7. Source audit

### `literature-checked`

The locally [pinned Bailey--Borwein--Plouffe
PDF](../theory/pi-quantitative-block-hitting/library/t4/bbp-1997.pdf) has
SHA-256
`e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`.
Direct inspection on **2026-08-13 UTC** confirms that its Theorem 1 states
the base-16 four-pole series used in (A1). It does not state the present
3-adic decimation or any decimal-distribution theorem.

The cited [Delaygue--Rivoal--Roques record](https://arxiv.org/abs/1309.5902)
was also checked directly on
**2026-08-13 UTC**. Its abstract concerns Dwork congruences for generalized
hypergeometric series with rational parameters and mirror-map integrality;
it does not directly supply (A10) or complementary CRT control. The primary
report appropriately makes no application claim.

The bounded searches for `"BBP" "3-adic" decimation`, `"BBP" p-adic
congruence truncated sums`, `arctangent partial sum p-adic congruence`, and
`Dwork truncated sum congruence hypergeometric rational parameters` were
also repeated on that date. They exposed generic BBP references and Dwork or
hypergeometric congruence literature, but no source stating (A10), (A18), or
joint control for the complementary BBP coordinates.

This is a bounded applicability check, not a novelty claim.

## 8. Independent replay

The independent checker reconstructs every pole separately, verifies the
negative-cutoff boundaries, calculates endpoint units by localized modular
sums, enumerates both grid-fibre regimes, recompiles T74 under `--trust=0`,
and checks the declaration/audit sets. Its output was:

```text
claim_status=experiment
pinned_artifact_checks=7
partial_fraction_checks=2049
fold_identity_checks=16388
exact_term_identity_checks=1028
lte_and_exact_valuation_checks=17416
nonfold_integrality_checks=29131
negative_cutoff_boundary_checks=6
finite_sum_decimation_checks=730
symbolic_endpoint_checks=89
beta_nesting_checks=10
fixed_exponent_inverse_checks=3180
grid_map_checks=9842
exceptional_e4_drop_three_fibres=1
generic_drop_nine_fibres=2460
positive_tail_coefficient_checks=4096
real_shadow_checks=90
t74_theorem_count=12
t74_registered_theorem_count=12
t74_trust_zero=PASS
t74_axioms=Classical.choice,Quot.sound,propext
beta_rows=e2:M4:pre2:post2;e4:M49:pre38:post23;e6:M454:pre524:post185;e8:M4099:pre4898:post914;e10:M36904:pre57386:post18410;e12:M332149:pre175484:post175874
asserts_joint_crt_control=false
asserts_fixed_return=false
asserts_v1=false
status=PASS_WITH_BOUNDARY_QUALIFICATION
```

These bounded checks have status `experiment`; they do not replace the
all-depth derivations above. Reproduction from the repository root:

```bash
python work/ultrapi-resume/bbp_three_primary_decimation_20260813_independent_check.py
```

No primary report, primary checker, `ultrapi.md`, TheoryLib file, audit file,
or verification gate was edited by this independent audit.

## 9. V1 boundary and coordination

The decimation creates coherent 3-adic endpoint units, and the real-shadow
bound shows that the relevant rational rows approximate genuine pi-orbit
segments. The uncontrolled complementary CRT phase is still synchronized
with the selected exponent. It could cancel every isolated 3-primary grid;
neither nesting nor shadowing supplies a joint discrepancy estimate.
Therefore V1 remains a `conjecture`.

This audit registered descendant-area watch
`ultrapi-three-primary-decimation-independent-20260813` on
`local:pi-digits` for agent
`codex-ultrapi-three-primary-decimation-independent`. Its initial poll was
empty at cursor and delivered sequence 57,290. Its final poll after artifact
hygiene was also empty at that cursor and delivered sequence, so there was
no event to acknowledge. Observation events are coordination signals only
and were not used as mathematical evidence.
