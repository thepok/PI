# Even-depth BBP dyadic mixing: exact fixed-level bijection and diagonal barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_high_dyadic_archimedean_separator_20260813.md](bbp_high_dyadic_archimedean_separator_20260813.md),
  SHA-256
  `d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3`;
- [bbp_high_dyadic_archimedean_separator_20260813_check.py](bbp_high_dyadic_archimedean_separator_20260813_check.py),
  SHA-256
  `69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8`;
- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  `9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  This addendum proves no decimal return
for pi.

The new result has status `proof sketch`.  It sharpens fixed-level
permutation of the two-adic BBP function to the **actual selected dyadic
coordinate**.  On every even sevenfold depth \(n=2m\), define

\[
                         H(m)=25^mF(14m+1).                    \tag{1}
\]

Then for distinct nonnegative integers \(m,m'\),

\[
             \boxed{v_2(H(m)-H(m'))=1+v_2(m-m').}             \tag{2}
\]

Consequently, for every fixed \(s\geq1\), \(H\) maps
\(\mathbb Z/2^{s-1}\mathbb Z\) bijectively onto all odd residues modulo
\(2^s\).  Whenever \(s\leq54m\), these are exactly the low \(s\) bits of the
complete reduced dyadic coordinate \(w_{2m}\) of the selected sevenfold BBP
numerator.

This is deterministic, coefficient-specific fixed-level mixing.  It does
not control the needed diagonal \(s=54m\): a full period at that level has
\(2^{54m-1}\) even-depth samples.  Moreover, the frozen separator preserves
the complete dyadic coordinate at every depth while having eventual zero
carries and only the all-nine color.  Thus (2) is genuine new structure but
cannot alone prove a colored return or V1.

The finite replay is an `experiment`.  Nothing here is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.

## 1. Exact selected coordinate

Use the four-pole coefficient

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}.                         \tag{3}
\]

The frozen all-depth audit defines the two-adic analytic function

\[
 F(X)=\sum_{j\geq0}16^ja(X-1-j)                    \tag{4}
\]

and proves

\[
 F(0)=0,\qquad
 v_2(F(x)-F(y))=v_2(x-y)\quad(x,y\in\mathbb Z_2).  \tag{5}
\]

The frozen high-dyadic report also proves the ordinary rational identity

\[
                         F(N+1)={A_N\over L_N}=16^NB_N,        \tag{6}
\]

where \(L_N,A_N,B_N\) are the exact common denominator, selected numerator,
and BBP partial sum.

At sevenfold depth put

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n},\qquad
 r_n=v_2(7n+1),\qquad\kappa_n=27n-r_n.              \tag{7}
\]

If \([x]_{2^s}\) denotes the canonical residue of a two-integral rational,
the complete reduced dyadic coordinate is

\[
 w_n=\left[\,{5^nF(7n+1)\over2^{r_n}}\,\right]_{2^{\kappa_n}}. \tag{8}
\]

For \(n=2m\), the integer \(14m+1\) is odd, hence \(r_{2m}=0\) and
\(\kappa_{2m}=54m\).  Equations (1) and (8) give

\[
                         \boxed{w_{2m}=[H(m)]_{2^{54m}}.}      \tag{9}
\]

This is why the theorem below concerns the selected coordinate itself, not
merely an auxiliary value of \(F\).

## 2. Unit parity and the lifting identity

Equation (5) with \(y=0\) gives

\[
                         v_2(F(x))=v_2(x).                     \tag{10}
\]

In particular \(F(14m+1)\) is a two-adic unit for every \(m\geq0\), so
\(H(m)\) is odd modulo every positive power of two.

For every positive integer \(d\),

\[
                         v_2(25^d-1)=3+v_2(d).                 \tag{11}
\]

Here is an elementary proof, including both parity cases.  Write
\(d=2^tu\) with \(u\) odd.  The factorization

\[
 25^u-1=(25-1)(1+25+\cdots+25^{u-1})
\]

has first-factor valuation \(v_2(24)=3\), while the second factor is a sum
of an odd number of odd terms and is therefore odd.  Thus
\(v_2(25^u-1)=3\).  At each doubling,

\[
 25^{2e}-1=(25^e-1)(25^e+1),\qquad25^e+1\equiv2\pmod8,
\]

so the valuation increases by exactly one.  After \(t\) doublings this is
(11).  This is the needed special case of the lifting-the-exponent identity;
no asymptotic input is involved.

## 3. Scaled isometry proof

Let \(m,m'\geq0\).  If \(m=m'\), then \(H(m)=H(m')\) trivially; all
congruence statements below include this case.  Now suppose \(m\ne m'\).
Interchange the two indices if necessary, so \(m>m'\), and put \(d=m-m'>0\).
From (1),

\[
\begin{aligned}
 H(m)-H(m')=25^{m'}\bigl(&25^d(F(14m+1)-F(14m'+1))\\
                         &+(25^d-1)F(14m'+1)\bigr).            \tag{12}
\end{aligned}
\]

The outer factor is a unit.  By (5), the first term in parentheses has
valuation

\[
 v_2(14(m-m'))=1+v_2(d).                             \tag{13}
\]

By (10)--(11), the second has valuation

\[
                         3+v_2(d).                  \tag{14}
\]

The valuations in (13) and (14) differ by two.  The equality case of the
ultrametric inequality therefore says that their sum has the smaller
valuation.  The unit factor \(25^{m'}\) changes nothing, proving (2).

No cancellation assumption is hidden here: unequal valuations make the
conclusion exact for every distinct pair.

## 4. Exact bijection at each fixed level

Fix \(s\geq1\).  For any \(m,m'\geq0\), equality is trivial when
\(m=m'\); otherwise (2) gives

\[
\begin{aligned}
 H(m)\equiv H(m')\pmod {2^s}
 &\iff 1+v_2(m-m')\geq s\\
 &\iff m\equiv m'\pmod {2^{s-1}}.                  \tag{15}
\end{aligned}
\]

Thus \(H\bmod2^s\) induces an injection from
\(\mathbb Z/2^{s-1}\mathbb Z\).  Every output is odd by (10).  The source
and the set of odd residues modulo \(2^s\) both have \(2^{s-1}\) elements,
so the injection is a bijection:

\[
 \boxed{
 H:\mathbb Z/2^{s-1}\mathbb Z
   \;\longrightarrow\;(\mathbb Z/2^s\mathbb Z)^\times
 \text{ is bijective}.}                            \tag{16}
\]

The notation on the right is harmless for powers of two: its elements are
exactly the odd residues.  At the edge case \(s=1\), the source is
\(\mathbb Z/1\mathbb Z\), a singleton; the target is the singleton
\(\{1\}\bmod2\).  Equation (10) maps the former to the latter, so (16)
holds without a hidden \(s\geq2\) restriction.

Combining (9) and (16), for every fixed \(s\geq1\), any complete block of
\(2^{s-1}\) consecutive values of \(m\) lying far enough to satisfy
\(54m\geq s\) makes the actual coordinates \(w_{2m}\bmod2^s\) run through
every odd residue exactly once.

## 5. Why the diagonal remains open

The theorem is uniform in \(m\) only after \(s\) is fixed.  The complete
coordinate at even depth \(2m\) has \(54m\) bits.  Substituting the diagonal
precision \(s=54m\) into (16) makes one full period contain

\[
                         2^{54m-1}                 \tag{17}
\]

even-depth samples.  At depth \(2m\), the selected sequence supplies one
sample, not an exponentially long block at that same precision.  Therefore
fixed-level bijection does not locate \(w_{2m}\) in any prescribed moving
cell and gives no Archimedean estimate for \(w_{2m}/2^{54m}\).

The obstruction is structural, not just a missing constant.  The frozen
high-dyadic separator preserves the entire selected residue modulo
\(2^{27n}\), hence (9) and every fixed-level consequence (16), while its
centered states eventually have zero carries and only the all-nine endpoint
color for every fixed decimal period.  Any valid continuation must couple
the dyadic coordinate to selected odd data and an Archimedean least-residue
estimate.  The separate mixed-coordinate report shows that even a positive
linear mass of explicit odd prime coordinates is still insufficient.

Thus (16) is not a colored return and is not evidence that a particular
decimal word occurs in pi.

## 6. Exact replay

The companion
[bbp_even_depth_dyadic_mixing_20260813_check.py](bbp_even_depth_dyadic_mixing_20260813_check.py)
imports no earlier checker.  It reconstructs the rational four-pole
coefficient, evaluates \(F\) modulo powers of two, exhausts every pair in a
full period through eleven bits, includes the \(s=1\) singleton case, tests
208 adversarial distances with large two-adic orders and far offsets, and
reconstructs exact selected BBP numerators at positive even depths through
\(n=100\).

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813_check.py
```

Retained output:

```text
status: PASS
finite_claim_label: experiment
theorem_claim_label: proof sketch
maximum_fixed_precision: 11
maximum_even_sevenfold_depth: 100
f_zero_checks: 11
parity_checks: 2047
fixed_level_bijection_checks: 2047
scaled_isometry_checks: 698027
adversarial_scaled_isometry_checks: 208
two_adic_lifting_checks: 208
s_one_edge_checks: 2
exact_rational_identity_checks: 250
exact_selected_coordinate_checks: 250
full_diagonal_period_at_even_depth_m: 2^(54*m-1)
asserts_diagonal_mixing: false
asserts_colored_return: false
asserts_v1: false
```

Every bounded row has label `experiment`.  The all-index theorem is the
elementary valuation proof (10)--(16), conditional only on the frozen
`proof sketch` identities (5)--(6).

## 7. Literature, mathlib, and coordination boundary

This addendum makes no novelty claim.  Its only external mathematical input
is the BBP coefficient from Bailey--Borwein--Plouffe; the relevant source and
the bounded `literature-checked` normality audit are pinned in the frozen
reports.  The lifting calculation (11) is proved directly above.  No
published source found in that audit turns fixed-level two-adic permutation
into moving-precision Archimedean distribution for this selected numerator.

The local mathlib search in the frozen report found standard valuation and
finite-ring interfaces, but no theorem supplying the missing diagonal or
odd--dyadic--Archimedean correlation.  This addendum therefore adds no
declaration to the verified track.

The branch uses the descendant-area watch `ultrapi-high-dyadic-20260813` on
`local:pi-digits` for agent `codex-ultrapi-high-dyadic`.  Its polls were empty
at delivered sequence 56,947, so no event was acknowledged.  Observation
events are coordination signals only and were not used as evidence.

## Sharp handoff

The even-depth selected dyadic coordinate is now completely understood at
every fixed precision: it is a scaled isometry and an exact bijection onto
the odd residues.  This is stronger than knowing its valuation or knowing
that the auxiliary function \(F\) is a permutation.

The theorem stops exactly at the moving diagonal.  Its period there is
\(2^{54m-1}\), and an exact separator preserves all these dyadic facts while
failing every required color except the all-nine boundary.  A complete proof
still requires a mixed least-residue or exponential-sum estimate for the one
actual BBP numerator.  No such estimate is obtained here, so canonical V1
remains a `conjecture`.
