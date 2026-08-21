# BBP mixed odd--dyadic--Archimedean threshold

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_high_prime_coordinate_rigidity_20260813.md](bbp_high_prime_coordinate_rigidity_20260813.md),
  SHA-256
  `419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42`;
- [bbp_high_dyadic_archimedean_separator_20260813.md](bbp_high_dyadic_archimedean_separator_20260813.md),
  SHA-256
  `d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3`,
  with companion checker SHA-256
  `69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8`;
- [bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
  SHA-256
  `d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  No fixed return and no colored return
for pi is proved here.

This report gives a `proof sketch` audit of the proposed product-formula and
height route.  Its outcome is negative but sharp enough to change the next
research target.

1. The exact function \(F(7n+1)\) supplies the complete dyadic coordinate,
   and the explicit high-prime localization supplies genuine selected
   numerator coordinates at odd primes.  Putting both into the rational
   product formula still does not force a return.  The natural return
   determinant is a unit at 2; at a retained odd prime \(p\), it is a unit
   exactly unless \(10^m\equiv16\pmod p\).
2. There is an explicit mixed separator preserving every dyadic bit, both
   complete clean high-prime bands of total logarithmic mass
   \((10/3+o(1))M\), the corresponding next-depth forcing congruence, and
   asymptotically exact positive BBP forcing.  It nevertheless has only the
   all-nine boundary color and zero carries eventually.
3. The nearest-grid method has an exact mass threshold.  Statewise it works
   for any retained odd divisor of logarithmic mass

   \[
       \rho M,\qquad
       \rho<\rho_*:=6-{\log(2^{27}/5)\over7}
       =3.5563520053\ldots .                         \tag{1}
   \]

   The clean cross-depth construction below has
   \(\rho=10/3<\rho_*\).
4. At the other end, retaining **all** actual prime coordinates above the
   depth together with a BBP-quality real window makes the rational shadow
   unique: it is the actual \(B_M\).  Uniqueness reconstructs the open orbit;
   it does not distribute it.

Thus there is no product-formula breakthrough.  The precise missing input is
not another valuation, coordinate, denominator bound, or height uniqueness
lemma.  It is a simultaneous estimate for the least Archimedean residue of
the one actual numerator after its odd and dyadic coordinates have already
selected it.

The companion finite replay has label `experiment`.  Nothing here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Normalized targets and exact coordinates

Canonical V1 says that every finite word over
\(\{0,\ldots,9\}\), including words with leading zeroes, occurs contiguously
in the nonterminating decimal expansion of pi.  Empty words are vacuous.
It does not assert subsequence occurrence or occurrence of every infinite
tail.

Use

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}
\]

and write

\[
 L_M=\mathop{\rm lcm}(d_0,\ldots,d_M),\qquad
 A_M=\sum_{k=0}^M(120k^2+151k+47)16^{M-k}{L_M\over d_k},
 \qquad B_M={A_M\over16^ML_M}.                       \tag{2}
\]

At sevenfold depth put

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n},\qquad
 {V_n\over D_n}=10^nB_{7n}.                         \tag{3}
\]

The frozen high-dyadic report proves the ordinary rational identity

\[
 F(M+1)={A_M\over L_M}=16^MB_M,                     \tag{4}
\]

where \(F(X)=\sum_{j\geq0}16^ja(X-1-j)\) is the audited two-adic
function.  If \(r_n=v_2(7n+1)\) and
\(\kappa_n=27n-r_n\), the complete reduced dyadic coordinate of (3) is

\[
 w_n=\left[{5^nF(7n+1)\over2^{r_n}}\right]_{2^{\kappa_n}}. \tag{5}
\]

Nothing dyadic remains hidden in (5).

For a fixed return, write the reduced generic partial sum as

\[
 B_M={P_M\over2^{K_M}R_M},\qquad
 D_M^{(0)}=2^{K_M-4},\qquad
 A_m^{(0)}={10^m-16\over16}=2^{m-4}5^m-1.           \tag{6}
\]

Here \(P_M,A_m^{(0)},R_M\) are odd.  The exact fixed-return target is

\[
 \min_{5\leq m\leq\lfloor(\log_{10}16)M\rfloor}
 \left\|{A_m^{(0)}P_M\over D_M^{(0)}R_M}\right\|_{\mathbb T}
 \longrightarrow0.                                 \tag{7}
\]

The frozen transfer theorem makes (7) equivalent to the fixed-sixteen
return, hence to V1.  Equation (7) is a normalization, not a proof.

## 2. Why the return determinant defeats the bare product formula

For a candidate nearest integer \(\ell\), the integer whose ordinary size
measures (7) is

\[
 E_{M,m,\ell}
 =A_m^{(0)}P_M-\ell D_M^{(0)}R_M.                  \tag{8}
\]

For all sufficiently large \(M\), \(D_M^{(0)}\) is even.  The first term in
(8) is odd and the second is even, so

\[
                         v_2(E_{M,m,\ell})=0.       \tag{9}
\]

Thus the complete dyadic coordinate (5) determines a very long **unit
residue** of (8); it does not make (8) small at the two-adic place.

Likewise, if \(p\mid R_M\), then \(P_M\) is a unit modulo \(p\) and

\[
 p\mid E_{M,m,\ell}
 \iff p\mid A_m^{(0)}
 \iff 10^m\equiv16\pmod p.                         \tag{10}
\]

The explicit high-prime coordinate of \(P_M\) is again a unit.  It supplies
the exact nonzero residue in (10), but no divisibility unless the independent
discrete-log condition happens to hold.  The rational product formula for
\(E_{M,m,\ell}\ne0\),

\[
 |E_{M,m,\ell}|_\infty\prod_p|E_{M,m,\ell}|_p=1,  \tag{11}
\]

therefore gives only the tautological integer lower bound
\(|E_{M,m,\ell}|_\infty\geq1\).  It does not force one of the \(O(M)\)
available exponents to make (8) small relative to the exponentially large
denominator.

The same defect occurs for a colored determinant.  If \(q=10^P-1\), \(r_n\)
is a reduced selected phase numerator, and \(p\mid D_n\) but
\(p\nmid q r_n\), then

\[
              qr_n-kD_n\equiv qr_n\not\equiv0\pmod p.         \tag{12}
\]

Knowing the exact local coordinate does not turn a requested real color
into local divisibility.

## 3. The clean retained high-prime modulus

At generic depth \(M\), take the two frozen disjoint prime bands

\[
\begin{aligned}
 \mathcal P_{1,M}={}&
 \{p:4M+3<p\leq8M+1,\ p\equiv1\pmod8\}\\
 &\cup\{p:4M+3<p\leq8M+5,\ p\equiv5\pmod8\},\\
 \mathcal P_{2,M}={}&
 \{p:(8M+5)/3<p\leq4M+3\},\\
 Q_M={}&\prod_{p\in\mathcal P_{1,M}\cup\mathcal P_{2,M}}p.
                                                               \tag{13}
\end{aligned}
\]

Every displayed \(p\) occurs exactly once in the reduced odd denominator
\(R_M\), and its actual additive numerator coordinate is explicitly
\(64\pmod p\) or \(-32\pmod p\), according to the frozen localization.
The prime number theorem in progressions gives

\[
 \log Q_M=(2+4/3+o(1))M=(10/3+o(1))M.              \tag{14}
\]

The stronger frozen denominator audit proves

\[
                         \log R_M=(6+o(1))M.        \tag{15}
\]

Since \(R_M\mid L_M\), equations (13)--(15) imply

\[
 \log{L_M\over Q_M}\geq(8/3+o(1))M.               \tag{16}
\]

The moving bands also have the exact seven-depth nesting needed below:

\[
 Q_{M+7}\mid Q_M{L_{M+7}\over L_M}.                \tag{17}
\]

Here is a factor-by-factor proof of (17), including the moving boundaries.
Assume \(M\geq8\) and take \(p\in Q_{M+7}\).

- If \(p\in\mathcal P_{1,M+7}\) and it is at most the corresponding old
  endpoint \(8M+1\) or \(8M+5\), then
  \(p>4(M+7)+3>4M+3\), so \(p\in\mathcal P_{1,M}\).  Otherwise write
  \(p=8k+1\) or \(p=8k+5\).  The old and new upper endpoints give
  \(M<k\leq M+7\); moreover \(p\) did not occur in any old pole.  Hence its
  new exponent occurs in \(L_{M+7}/L_M\).
- If \(p\in\mathcal P_{2,M+7}\) and \(p\leq4M+3\), then the larger new
  lower endpoint still implies \(p>(8M+5)/3\), so
  \(p\in\mathcal P_{2,M}\).  Now suppose \(p>4M+3\).  If
  \(p\equiv1\) or \(5\pmod8\), the bound
  \(p\leq4(M+7)+3\) puts it below the corresponding old first-band upper
  endpoint when \(M\geq8\), hence \(p\in\mathcal P_{1,M}\).  If
  \(p\equiv3\pmod4\), write \(p=4k+3\); then
  \(M<k\leq M+7\), so this is a genuinely new pole factor and divides
  \(L_{M+7}/L_M\).

The band primes are squarefree in \(L_{M+7}\), so the primewise alternatives
multiply to (17).  There are no omitted boundary cases: every odd prime is
either \(1,5\pmod8\) or \(3\pmod4\), and every inequality above retains the
strict/inclusive endpoint from (13).

## 4. Mixed separator with all dyadic bits and both clean prime bands

Let

\[
 t_n=-10^n(\pi-B_{7n})<0,
 \qquad
 t_{n+1}=10t_n+{K_n\over D_{n+1}}                 \tag{18}
\]

be the exact bounded zero-carry solution of the selected recurrence.  Put
\(M_n=2^{27n}Q_{7n}\) and \(C_n=L_{7n}/Q_{7n}\).  Equation (16) makes
\(C_n>1\) eventually.  Every member of the mixed progression has the form

\[
                         S=V_n+M_nh,\qquad h\in\mathbb Z.       \tag{19a}
\]

Every prime in \(Q_{7n}\) occurs to exponent one in \(L_{7n}\), so
\(\gcd(M_n,L_{7n})=Q_{7n}\).  Consequently

\[
 S\equiv V_n\pmod {L_{7n}}
 \quad\Longleftrightarrow\quad C_n\mid h.            \tag{19b}
\]

First choose \(h_0\) nearest to \((D_nt_n-V_n)/M_n\).  If
\(C_n\nmid h_0\), retain it.  If \(C_n\mid h_0\), use the closer of
\(h_0-1\) and \(h_0+1\).  At least one adjacent shift is admissible because
\(C_n>1\).  Denote the resulting integer in (19) by \(S_n^\diamond\).  Then

\[
 \boxed{
 S_n^\diamond\equiv V_n\pmod {\,2^{27n}Q_{7n}},\qquad
 S_n^\diamond\not\equiv V_n\pmod {L_{7n}}.}          \tag{19c}
\]

Put

\[
 e_n^\diamond={S_n^\diamond\over D_n},\qquad
 \eta_n=e_n^\diamond-t_n,\qquad
 r_n^\diamond=D_n+S_n^\diamond.                    \tag{20}
\]

The nearest unrestricted shift is within half a mesh; moving to an adjacent
shift costs at most one more mesh.  The normalized mesh and (16) give

\[
 |\eta_n|\leq{3Q_{7n}\over2L_{7n}}
 \leq\exp(-(56/3+o(1))n).                          \tag{21}
\]

The first omitted positive BBP term gives

\[
 |t_n|\geq{(5/2^{27})^n\over336(7n+1)^2}.          \tag{22}
\]

The exponent margin is strictly positive:

\[
 {56\over3}-\log(2^{27}/5)
 =1.5611307039\ldots>0.                             \tag{23}
\]

Consequently

\[
                         |\eta_n|/|t_n|\longrightarrow0,       \tag{24}
\]

and eventually \(-1/2<e_n^\diamond<0\).

The congruences (19c) preserve simultaneously:

- the complete raw dyadic coordinate modulo \(2^{27n}\), hence every bit of
  the reduced coordinate (5);
- the actual selected numerator coordinate at every prime in both bands
  (13); and
- every CRT character assembled from their product.

The inequality in (19c) also proves that the shadow is genuinely distinct:
at least one unretained odd coordinate differs from the actual complete
selected-numerator residue.

Define the alternative forcing

\[
 K_n^\diamond=S_{n+1}^\diamond-10\Lambda_nS_n^\diamond.       \tag{25}
\]

Equations (17), (19c), and the 28 dyadic powers contributed by
\(10\Lambda_n\) prove the complete next mixed congruence

\[
 \boxed{
 K_n^\diamond\equiv K_n
 \pmod {\,2^{27(n+1)}Q_{7(n+1)}}.}                 \tag{26}
\]

Moreover

\[
 {K_n^\diamond\over D_{n+1}}-{K_n\over D_{n+1}}
 =\eta_{n+1}-10\eta_n.                             \tag{27}
\]

The same comparison as (21)--(23), using the frozen positive lower bound for
\(K_n/D_{n+1}\), shows that (27) is exponentially small **relative** to the
true forcing.  In particular \(K_n^\diamond>0\) eventually.

Fix \(P\geq1\), set \(q=10^P-1\), and take \(n\) sufficiently large that
\(-1/2<qe_n^\diamond<0\).  Then the split color is

\[
 \left\lfloor q{r_n^\diamond\over D_n}+{1\over2}\right\rfloor=q. \tag{28}
\]

The exact phase quotient is nine:

\[
 10\Lambda_nr_n^\diamond+K_n^\diamond
 =9D_{n+1}+r_{n+1}^\diamond.                       \tag{29}
\]

Hence the colored carry is

\[
 9q+q-10q=0.                                        \tag{30}
\]

Thus every fixed period eventually sees only the all-nine boundary color and
zero carries, despite all the simultaneous data listed above.  This is an
alternative rational recurrence, not the BBP orbit and not a counterexample
concerning pi.

## 5. Exact separator threshold and the rigidity side

The preceding construction admits a useful mass ledger.  Suppose
\(Q_M'\mid R_M\) is any squarefree product of selected high-prime coordinates
with

\[
                         \log Q_M'=(\rho+o(1))M.     \tag{31}
\]

Ignoring only the optional cross-depth nesting, the same statewise nearest
selection has error

\[
 {3Q_{7n}'\over2L_{7n}}
 \leq\exp(-(7(6-\rho)+o(1))n).                     \tag{32}
\]

This worst-case mesh bound proves relative shadowing whenever its exponent is
positive:

\[
 7(6-\rho)>\log(2^{27}/5)
 \iff \rho<\rho_*                                  \tag{33}
\]

with \(\rho_*\) from (1).  The clean nested bands have
\(\rho=10/3\), leaving the margin (23).  Formula (33) is the exact threshold
of this nearest-grid estimate.  It is not an impossibility theorem for every
more structured construction at or above \(\rho_*\).

Retaining all actual prime coordinates above \(M\) is on the other side:
their logarithmic mass is \((5+o(1))M\).  The high-prime rigidity report
proves more directly that, once those coordinates, the complete dyadic
coordinate, and a BBP-quality real window are all imposed, the only rational
shadow is \(B_M\) itself.  There is no remaining CRT parameter to tune.

This creates a precise three-part boundary:

- up through both explicit bands, a full mixed zero-carry separator exists;
- beyond \(\rho_*\), the present relative-shadowing estimate no longer
  constructs one; and
- with every high prime and the BBP window, height proves uniqueness but no
  return.

Neither side forces (7).  The separator shows insufficiency below the
threshold; rigidity above it merely gives the actual open instance back.

## 6. Product formula applied to the separator difference

For completeness, put

\[
                         \Delta_n=S_n^\diamond-V_n.             \tag{34}
\]

Then

\[
                    2^{27n}Q_{7n}\mid\Delta_n.      \tag{35}
\]

Equation (19c) makes \(\Delta_n\ne0\).  The ordinary integer bound therefore
says

\[
                         |\Delta_n|_\infty
                         \geq2^{27n}Q_{7n}.          \tag{36}
\]

There is no conflict with the real shadowing (24).  Indeed

\[
 \Delta_n=D_n(e_n^\diamond-10^nB_{7n}),             \tag{37}
\]

and the second term is of order \(10^n\), whereas the first tends to zero.
Thus \(\Delta_n\) has the natural enormous selected-numerator height.  The
two-adic and retained odd local factors in the product formula are exactly
balanced by (36) and by the omitted odd cofactor.

The genuinely small real number \(D_n\eta_n\) is not a selected-numerator
difference: through (18), it contains pi.  It is irrational, so the rational
product formula cannot be applied to it.  Substituting that small number for
\(\Delta_n\) would silently change the object under study.

## 7. The exact missing simultaneous estimate

Let \(\ell_{M,m}\) be a nearest integer to the rational in (7).  The weakest
direct missing statement for the fixed-return route is

\[
 \boxed{
 \liminf_{M\to\infty}
 \min_{5\leq m\leq\lfloor(\log_{10}16)M\rfloor}
 { |A_m^{(0)}P_M-\ell_{M,m}D_M^{(0)}R_M|
  \over D_M^{(0)}R_M}=0.}                           \tag{38}
\]

This is not supplied by height uniqueness.  It requires correlation between

- the diagonal dyadic unit selected by \(F(M+1)\);
- the explicit odd local residues of \(P_M\), including their synchronized
  discrete-log cancellation classes (10); and
- the least ordinary representative after multiplication by the same short
  orbit \(A_m^{(0)}\).

A stronger sufficient input would be cancellation, with a usable uniform
rate, in the actual coefficient-specific sums

\[
 \sum_{5\leq m\leq(\log_{10}16)M}
 e\!\left({hA_m^{(0)}P_M\over D_M^{(0)}R_M}\right). \tag{39}
\]

Factoring (39) into separate dyadic and odd characters does not help: both
characters are driven by the same \(A_m^{(0)}\), and neither frozen result
controls their product.  Equation (38), or an estimate such as (39), is the
remaining mixed odd--dyadic--Archimedean theorem.  Merely adding enough
coordinates to reconstruct \(P_M\) exactly does not prove it.

## 8. Independent exact replay

The companion
[bbp_mixed_coordinate_height_separator_20260813_check.py](bbp_mixed_coordinate_height_separator_20260813_check.py)
has SHA-256
`3de7bd7be4df346743ff9d9a61dd8b90475ca362ea184b61d76e2a274383458d`.
It imports neither frozen checker and independently rebuilds the four-pole
LCMs and selected numerators, the complete dyadic coordinate, both retained
prime bands, and the mixed nearest-grid recurrence with exact `Fraction`
arithmetic.

It verifies each retained prime survives reduction, every state and forcing
congruence, the seven-depth nesting (17), the exact quotient nine, all-nine
colors and zero carries for five periods, the forbidden full-odd shift class
under adversarial nearest points, 81,664 generic moving-band boundary cases,
and the ordinary-height balance (36).  Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_check.py
```

Retained output:

```text
status: PASS
bounded_replay_label: experiment
construction_label: proof sketch
depth_range: [18, 42]
bbp_depth_range: [126, 294]
rational_tail_cutoff: 56
retained_prime_mass_rho: 10/3
rho_star_from_log_R_equals_6M: 3.5563520053307967
positive_exponent_margin: 1.5611307039822435
endpoint_checks: 75
adversarial_selector_checks: 150
band_nesting_boundary_checks: 81664
high_prime_coordinate_checks: 9932
state_checks: 175
transition_checks: 168
color_and_zero_carry_checks: 370
product_formula_balance_checks: 50
minimum_observed_retained_log_mass_over_depth: 3.156331629900669
minimum_observed_free_log_mass_over_depth: 2.6793957611946957
maximum_relative_state_error: 1.1506155724375323e-12
maximum_relative_forcing_error: 1.1506155735680529e-12
preserves_complete_dyadic_coordinate: true
preserves_positive_linear_high_prime_mass: true
preserves_complete_next_mixed_forcing_class: true
asserts_fixed_return: false
asserts_all_color_return: false
asserts_v1: false
```

All finite rows are only an `experiment`.  The asymptotic separator is the
`proof sketch` in Sections 3--5, dependent on the frozen BBP identities and
prime-number estimates explicitly cited there.

## Sharp handoff

The mixed product-formula route does not close V1.  The complete dyadic
coordinate is now exact, and a linear mass of actual odd numerator
coordinates can be retained at the same time without forcing even a second
color.  If all high-prime coordinates and the tight real window are retained,
height removes the alternative shadows but only reconstructs the actual BBP
point.

The next useful attack must address (38) or (39) for that selected point.  A
new denominator estimate, one-place valuation, CRT reconstruction, or
product formula without a genuinely small mixed algebraic form will repeat
one of the two audited sides of the threshold and cannot by itself prove V1.
