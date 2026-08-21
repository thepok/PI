# Independent audit: BBP mixed coordinate/height separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
'2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825'.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Audited frozen artifacts:

- [bbp_mixed_coordinate_height_separator_20260813.md](bbp_mixed_coordinate_height_separator_20260813.md),
  SHA-256
  '950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820';
- [bbp_mixed_coordinate_height_separator_20260813_check.py](bbp_mixed_coordinate_height_separator_20260813_check.py),
  SHA-256
  '6549b99503cb34aaf757f0c428702b3797714144d0bc8e1f77a336fe965d6846'.

Dependency hashes were independently checked, including the source, the
high-prime report, the high-dyadic report and checker, and the actual
odd-quotient report. The audit did not edit either primary artifact or
'ultrapi.md'.

## Verdict and claim boundary

**Audit verdict: `PASS`. The central mixed-separator construction is
supported as a 'proof sketch'.** The exact congruences, the \(3/2\)-mesh
selector, the moving-band nesting, the positive relative forcing estimate,
the all-nine colors, the zero carries, and the strict worst-case mesh
threshold all rederive correctly. The primary and independent exact replays
pass.

Canonical V1 remains a 'conjecture'. No return for pi is proved. The finite
replay is an 'experiment'; nothing in this branch is 'machine-checked', a
'candidate resolution', or a 'verified resolution'.

The initial audit found two overstatements and one dependency-pin omission.
They are resolved in the frozen artifacts audited above:

1. The report now states the exact odd-prime exception condition
   \(10^m\equiv16\pmod p\), rather than the unsupported phrase “almost every”
   when \(m\) grows with the BBP depth.
2. The threshold statement now says that the worst-case mesh bound proves
   relative shadowing whenever its exponent is positive. It does not assert
   failure when the bound is inconclusive.
3. The primary checker now pins
   'bbp_actual_odd_quotient_attack.md' at SHA-256
   'd77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc'.

The corrected lines and hashes were inspected directly before the final
replay. No qualification remains open.

## 1. Exact algebra and complete selected coordinates

Let

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},
\]

and let \(L_M,A_M,B_M\) have the meanings in the primary report. Direct
substitution gives

\[
 {5^nA_{7n}\over2^{27n}L_{7n}}=10^nB_{7n}.          \tag{A1}
\]

The frozen high-dyadic identity
\(F(M+1)=A_M/L_M=16^MB_M\), together with
\(v_2(F(M+1))=v_2(M+1)\), therefore yields exactly the displayed complete
reduced dyadic coordinate. There is no lost bit: before dividing by
\(2^{v_2(7n+1)}\), the necessary raw precision is \(2^{27n}\).

At consecutive sevenfold depths, direct expansion of \(A_{7n+7}\) gives

\[
 D_{n+1}=\Lambda_nD_n,
 \qquad V_{n+1}=10\Lambda_nV_n+K_n,                 \tag{A2}
\]

where \(\Lambda_n=2^{27}L_{7n+7}/L_{7n}\). Thus the selected tail
\(t_n=-10^n(\pi-B_{7n})\) satisfies

\[
 t_{n+1}=10t_n+K_n/D_{n+1}.                         \tag{A3}
\]

These identities are ordinary rational algebra once the BBP formula is
fixed.

## 2. Prime bands, exponent one, and logarithmic mass

The two bands are disjoint: the second ends at \(4M+3\), while the first is
strictly above \(4M+3\). Their logarithmic masses follow from the prime
number theorem in arithmetic progressions:

\[
\begin{aligned}
 \log Q_{1,M}
 &=\bigl((8-4)/\varphi(8)+(8-4)/\varphi(8)+o(1)\bigr)M
   =(2+o(1))M,\\
 \log Q_{2,M}&=(4-8/3+o(1))M=(4/3+o(1))M.
\end{aligned}                                       \tag{A4}
\]

Hence \(\log Q_M=(10/3+o(1))M\).

Every band prime is larger than \((8M+5)/3\). Each odd linear pole is at
most \(8M+5<3p\), so a divisible pole must equal \(p\), not a higher odd
multiple. The residue class of \(p\) then selects exactly one of
\(4k+3,8k+1,8k+5\). Consequently \(v_p(L_M)=1\). Localizing the one
singular summand gives

\[
 \gamma_{M,p}\equiv
 \begin{cases}
 64\pmod p,&p\equiv1\pmod4,\\
 -32\pmod p,&p\equiv3\pmod4.
 \end{cases}                                       \tag{A5}
\]

These residues are nonzero for the odd primes in the bands, so the factor
survives with exponent one in the reduced odd denominator \(R_M\).

The frozen odd-quotient analysis gives \(\log R_M=(6+o(1))M\). One can
also recover the matching upper bound for \(L_M\): above \(4M+O(1)\), its
prime support contains only the classes \(1,5\pmod8\), up to \(8M+O(1)\),
while prime powers contribute only \(o(M)\). Thus

\[
 \log L_M=(6+o(1))M,
 \qquad
 \log(L_M/Q_M)=(8/3+o(1))M.                        \tag{A6}
\]

The last equality justifies both the available mesh and the later threshold;
using only \(R_M\mid L_M\) gives the sufficient lower bound used in the
primary text.

## 3. Seven-depth nesting, including boundaries

For \(M\ge8\), take \(p\in Q_{M+7}\).

- In the new first band, if \(p\) is below the old endpoint for its class
  modulo eight, it is still in the old first band. Otherwise
  \(p=8k+1\) or \(8k+5\) with \(M<k\le M+7\), and \(p\) is a genuinely
  new pole factor.
- In the new second band, if \(p\le4M+3\), it remains in the old second
  band. If \(p>4M+3\) and \(p\equiv1,5\pmod8\), then
  \(p\le4M+31\) lies below the corresponding old first-band endpoint for
  \(M\ge8\), so it is in the old first band. In the remaining classes
  \(p\equiv3\pmod4\), write \(p=4k+3\); then \(M<k\le M+7\), so it is a
  new pole factor.

Because the new band is squarefree, these alternatives multiply to

\[
 Q_{M+7}\mid Q_M{L_{M+7}\over L_M}.                 \tag{A7}
\]

Strict and inclusive endpoints cause no missing case. The independent
replay checked every applicable prime for all \(8\le M\le4000\), including
18,413 new-pole alternatives.

## 4. The forbidden-class selector

At depth \(7n\), put

\[
 \mathcal M_n=2^{27n}Q_{7n},\qquad
 C_n=L_{7n}/Q_{7n}.
\]

Since \(L_{7n}\) is odd and every retained prime has exponent one,

\[
 \gcd(\mathcal M_n,L_{7n})=Q_{7n}.                  \tag{A8}
\]

For \(S=V_n+\mathcal M_nh\), cancellation of \(Q_{7n}\) gives the exact
equivalence

\[
 S\equiv V_n\pmod {L_{7n}}
 \quad\Longleftrightarrow\quad C_n\mid h.           \tag{A9}
\]

Equation (A6) makes \(C_n>1\) eventually. Choose a nearest integer \(h_0\)
to the desired real shift. If \(h_0\) is forbidden, both adjacent integers
are admissible because \(C_n>1\). A closest adjacent choice has distance at
most \(1/2+1=3/2\). Therefore the resulting \(S_n^\diamond\) is distinct
from \(V_n\), preserves the full mixed congruence, changes the full odd
ambient class, and satisfies

\[
 |\eta_n|\le {3Q_{7n}\over2L_{7n}}
 =\exp(-(56/3+o(1))n).                              \tag{A10}
\]

The independent replay checked half-integer ties, negative targets, every
forbidden modulus \(2\le C\le301\), and nearby forbidden multiples. It also
checked (A9) directly on each constructed row.

## 5. Relative state and forcing estimates

For \(k\ge1\), clearing denominators gives

\[
\begin{aligned}
 21k^2\operatorname{num}(a(k))-\operatorname{den}(a(k))
 &=2008k^4+2147k^3+275k^2-194k-15>0,\\
 \operatorname{den}(a(k))-k^2\operatorname{num}(a(k))
 &=392k^4+873k^3+665k^2+194k+15>0.
\end{aligned}                                       \tag{A11}
\]

The first polynomial is already positive at \(k=1\), and separating its
only negative terms makes positivity for all \(k\ge1\) immediate. Hence
\(1/(21k^2)<a(k)<1/k^2\). Positivity of the BBP tail now yields

\[
 {\lambda^n\over336(7n+1)^2}
 \le |t_n|
 \le {\lambda^n\over15(7n+1)^2},
 \qquad \lambda={5\over2^{27}}.                    \tag{A12}
\]

Combining (A10) and (A12),

\[
 {|\eta_n|\over|t_n|}
 \ll n^2\exp\!\left(-
 \left({56\over3}-\log(2^{27}/5)+o(1)\right)n\right)
 \longrightarrow0,                                 \tag{A13}
\]

because the exponent margin is
\(1.5611307039822435\ldots>0\). Thus
\(-1/2<e_n^\diamond<0\) eventually.

Writing \(\Delta_n=S_n^\diamond-V_n\), equation (A7) and
\(v_2(10\Lambda_n)=28\) give

\[
 \Delta_{n+1}-10\Lambda_n\Delta_n
 \equiv0\pmod {2^{27(n+1)}Q_{7(n+1)}}.              \tag{A14}
\]

This is exactly the claimed forcing congruence. Also

\[
 {K_n^\diamond-K_n\over D_{n+1}}
 =\eta_{n+1}-10\eta_n.                              \tag{A15}
\]

The first newly added BBP term and (A11) give

\[
 {K_n\over D_{n+1}}
 \ge {5\over168(7n+1)^2}\lambda^n.                 \tag{A16}
\]

Equations (A10), (A15), and (A16) prove exponentially vanishing relative
forcing error and hence \(K_n^\diamond>0\) eventually.

## 6. Colors and carries

Fix \(P\ge1\) and put \(q=10^P-1\). From (A13), eventually
\(-1/2<qe_n^\diamond<0\). Since
\(r_n^\diamond/D_n=1+e_n^\diamond\), the centered color is exactly \(q\).
The recurrence definitions give the ordinary integer identity

\[
 10\Lambda_nr_n^\diamond+K_n^\diamond
 =10D_{n+1}+S_{n+1}^\diamond
 =9D_{n+1}+r_{n+1}^\diamond.                        \tag{A17}
\]

Thus the quotient is nine and the centered carry is
\(9q+q-10q=0\). This establishes the advertised separator behavior for
every fixed period. It is an alternative rational recurrence, not the BBP
orbit.

## 7. Product formula and the exact local condition

In reduced form let

\[
 B_M={P_M\over2^{K_M}R_M},\quad
 D_M^{(0)}=2^{K_M-4},\quad
 A_m^{(0)}={10^m-16\over16}.
\]

For sufficiently large \(M\), \(D_M^{(0)}\) is even, whereas
\(P_M,R_M,A_m^{(0)}\) are odd. Therefore

\[
 E=A_m^{(0)}P_M-\ell D_M^{(0)}R_M
\]

is a nonzero odd integer for every \(\ell\). For every \(p\mid R_M\),

\[
 p\mid E
 \quad\Longleftrightarrow\quad
 p\mid A_m^{(0)}
 \quad\Longleftrightarrow\quad
 10^m\equiv16\pmod p.                               \tag{A18}
\]

This exact equivalence is now the wording used by the primary report and
supports its product-formula obstruction. It is important not to replace it
by “almost every” when \(m\) varies with \(M\): the logarithmic mass of the
exceptional distinct primes is bounded above only by

\[
 \log|10^m-16|\le m\log10+O(1),                     \tag{A19}
\]

which is linear in \(M\) on the proportional row, not \(o(M)\). The exact
exception condition (A18) is the safe statement.

For the separator difference, \(\Delta_n\ne0\) and
\(2^{27n}Q_{7n}\mid\Delta_n\), hence
\(|\Delta_n|_\infty\ge2^{27n}Q_{7n}\). This is exactly the ordinary-height
compensation required by the rational product formula. By contrast,
\(D_n\eta_n\) contains a nonzero rational multiple of pi and is
transcendental, so substituting it would change the object and invalidate
the rational product-formula argument.

## 8. What the threshold does and does not prove

If a squarefree retained divisor \(Q'_M\mid R_M\) has
\(\log Q'_M=(\rho+o(1))M\), equations (A6) and the same selector give the
worst-case bound

\[
 |\eta_n|\le
 \exp(-(7(6-\rho)+o(1))n).                          \tag{A20}
\]

Comparison with (A12) certifies relative shadowing precisely when

\[
 7(6-\rho)>\log(2^{27}/5),
 \qquad
 \rho<6-{\log(2^{27}/5)\over7}
 =3.5563520053307967\ldots .                        \tag{A21}
\]

For the clean bands, \(\rho=10/3\), and the strict margin is the value in
(A13). If (A21) fails, the worst-case upper bound no longer proves relative
shadowing. It does not give a lower bound on the actual selected error, so
it is not an impossibility theorem for the nearest choice or for any more
structured construction.

## 9. Independent exact replay

The independent checker is
[bbp_mixed_coordinate_height_separator_20260813_independent_check.py](bbp_mixed_coordinate_height_separator_20260813_independent_check.py).
Its SHA-256 is
'c95daf68ea535cc3fb41b30cedab7c4723bd3eca0776bea364fac8073b365fe0'.
It imports no branch checker and uses only integers, 'Fraction', modular
inverses, a sieve, and elementary arithmetic. It additionally checks the
actual clean local coordinates \(64,-32\), the determinant equivalence at
every sampled odd denominator prime, broad negative/tie selector cases, and
all frozen dependency hashes.

Run from the repository root:

~~~bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_independent_check.py
~~~

Retained output:

~~~text
status: PASS
bounded_claim_label: experiment
audited_construction_label: proof sketch
coefficient_bound_checks: 20000
band_disjointness_checks: 7322639
band_nesting_checks: 2858057
band_nesting_old_checks: 2839644
band_nesting_new_pole_checks: 18413
band_mass_ratio_at_depth_4000: 3.3033234982788384
adversarial_selector_checks: 72900
gcd_equivalence_checks: 777
exact_state_checks: 189
localized_coordinate_checks: 9835
transition_checks: 160
color_and_zero_carry_checks: 800
determinant_parity_checks: 5554
determinant_local_equivalence_checks: 438014
rho_star: 3.5563520053307967
clean_exponent_margin: 1.5611307039822435
maximum_relative_state_error: 1.1506155724375323e-12
maximum_relative_forcing_error: 1.1506155735680529e-12
asserts_fixed_return: false
asserts_all_color_return: false
asserts_v1: false
~~~

All bounded checks are only an 'experiment'. The all-index and asymptotic
claims supported as a 'proof sketch' are the elementary derivations in
Sections 1--8 together with the frozen prime-number and BBP inputs.

## Coordination record

This audit registered descendant-area watch
'ultrapi-mixed-separator-independent-audit-20260813' on 'local:pi-digits'
for agent 'codex-ultrapi-mixed-separator-independent-audit'. Its initial
and final polls were empty at cursor and delivered sequence 57,018, so there
was no event to acknowledge. Observation events are coordination signals
only and are not mathematical evidence.

## Sharp handoff

With all audit corrections applied and frozen, the mixed separator is a
sound negative 'proof sketch': complete dyadic data plus clean odd-prime mass
\((10/3+o(1))M\), exact next-depth mixed forcing, and BBP-relative real
accuracy still permit eventual all-nine color and zero carries. The product
formula sees unit determinants rather than forced local smallness. This
does not advance canonical V1 beyond a 'conjecture'; the missing theorem
remains an estimate for the actual selected numerator's short decimal orbit.
