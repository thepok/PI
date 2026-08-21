# Second independent audit: BBP rational-phase density separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable target is local and human-authored; it has no external source
URL, and none is invented here.

Frozen artifacts audited:

- [bbp_rational_phase_density_separator_20260813.md](bbp_rational_phase_density_separator_20260813.md),
  SHA-256
  1fa0054d89852630c573ad9eee5bd5ae59a442b34809343f7ca9bb7dc1fbc198;
- [bbp_rational_phase_density_separator_20260813_check.py](bbp_rational_phase_density_separator_20260813_check.py),
  SHA-256
  72dfd913b3532bfe41e1df9a87ebbb3000f6fe1d179af4edbc0163d2a36cc3bc.

Second independent replay:

- [bbp_rational_phase_density_separator_20260813_second_independent_check.py](bbp_rational_phase_density_separator_20260813_second_independent_check.py),
  SHA-256
  7f76b9802318d89e1ae3f825e49049755e645e9d94f2fe730f2916ffeb99f96a.

## Verdict

**PASS, with two claim-boundary clarifications and no mathematical correction
to the displayed separator constructions.**

The following independently rederive:

- the exact rational forcing and unique bounded all-zero orbit;
- both constants in the leading asymptotics;
- the reduced-denominator size and exact two-primary exponent;
- the Jacobsthal lift to an exact-denominator rational phase;
- the raw centered-numerator valuation and integer recurrence;
- the pointwise relative-error exponent \(42+\log5\);
- the coherent power-of-two reset construction;
- its density-one exact forcing and reset exponent
  \(21-14\log2+\frac12\log5\);
- the product-height obstruction and fixed-difference scope.

The primary conclusion is correct as a 'proof sketch': these separator
models show that substantial denominator, valuation, size, sign, and local
forcing data do not generically force positive carry density. They do not
prove anything about the exact selected BBP numerators for pi, so canonical
V1 remains a 'conjecture'.

Two wording boundaries must remain explicit.

1. The pointwise model has exact reduced denominator \(Q_{n,P}\) and exact
   raw two-adic order at every late depth, while its forcing is exponentially
   close at every transition. The coherent model has forcing exactly equal
   to BBP on a density-one set, but proves only that its reduced denominator
   divides \(D_n\). No single construction in the report is shown to have
   both exact \(Q_{n,P}\) at every depth and density-one exact forcing.
2. The pointwise proof bounds the forcing difference at every transition and
   the uniqueness argument excludes eventual equality. It does not prove
   that the difference is nonzero at every individual transition. The
   sentence saying that it “changes the forcing at every transition” should
   be read as “is allowed to change it at every transition.” This does not
   affect any estimate or separator conclusion.

The independent checker has status 'experiment'. The inherited source audit
is 'literature-checked'. Nothing here is 'machine-checked', a
'candidate resolution', or a 'verified resolution'.

## 1. Exact forcing and the unique bounded zero-carry orbit

Fix \(P\geq1\), put \(q=10^P-1\), and retain

\[
a(k)={120k^2+151k+47\over
(2k+1)(4k+3)(8k+1)(8k+5)},\qquad
B_m=\sum_{k=0}^m{a(k)\over16^k}.                    \tag{A1}
\]

For

\[
x_n=q10^nB_{7n},\qquad
\delta_n=q10^{n+1}(B_{7n+7}-B_{7n}),                \tag{A2}
\]

one has \(x_{n+1}=10x_n+\delta_n\) exactly. Positivity follows because the
combined coefficient in (A1) has positive numerator and denominator for
every \(k\geq0\).

Set

\[
\lambda={10\over16^7}={5\over2^{27}},\qquad
R(n)=\sum_{j=1}^7{a(7n+j)\over16^j}.                \tag{A3}
\]

Directly splitting the seven new summands gives

\[
\delta_n=10q\lambda^nR(n),\qquad
{\delta_{n+1}\over\delta_n}
=\lambda{R(n+1)\over R(n)}.                         \tag{A4}
\]

Since \(a\) is rational, \(R\) is a positive rational function. Thus (A4)
really is a first-order polynomial-coefficient recurrence after clearing
fixed rational-function denominators.

The phase

\[
t_n=-q10^n(\pi-B_{7n})                               \tag{A5}
\]

satisfies

\[
t_{n+1}-10t_n=\delta_n.                              \tag{A6}
\]

It is negative and tends to zero by the positive BBP tail bound. If another
solution of (A6) differs by \(d_n\), then \(d_{n+1}=10d_n\), so boundedness
forces \(d_n=0\). This establishes uniqueness. Each \(t_n\) is irrational,
because \(B_{7n}\) is rational and pi is irrational. Hence a rational
bounded phase cannot use the exact forcing with zero carries from some final
depth onward. This yields infinitude of resets, not their positive density.

The second independent checker verifies (A6) symbolically: it represents
\(t_n\) by its coefficient of pi and its rational part, so cancellation of
the irrational symbol is exact rather than numerical.

## 2. Independent derivation of the leading scales

The degrees and leading coefficients in (A1) give

\[
a(k)={15\over64k^2}\left(1+O(k^{-1})\right).         \tag{A7}
\]

For the full tail, put \(m=7n\). Uniformly for fixed \(j\),
\(a(m+j)=15/(64m^2)(1+O(n^{-1}))\), and geometric domination permits
summation. Since

\[
\sum_{j\geq1}16^{-j}={1\over15},\qquad
64(7n)^2=3136n^2,
\]

one obtains

\[
\pi-B_{7n}
={16^{-7n}\over3136n^2}\left(1+O(n^{-1})\right).    \tag{A8}
\]

Multiplication by \(q10^n\) proves

\[
t_n=-{q\over3136}\lambda^nn^{-2}
\left(1+O(n^{-1})\right).                           \tag{A9}
\]

For the seven-term increment,

\[
\sum_{j=1}^716^{-j}={1-16^{-7}\over15},
\]

so

\[
\delta_n
={10q(1-16^{-7})\over3136}\lambda^nn^{-2}
\left(1+O(n^{-1})\right)
={q(10-\lambda)\over3136}\lambda^nn^{-2}
\left(1+O(n^{-1})\right).                           \tag{A10}
\]

The independent replay checks the exact rational ratio in (A4) and obtains
0.9965579405... for the ratio of the true finite forcing to the leading
quantity in (A10) at its last checked transition. This is an 'experiment',
not the proof of (A10).

## 3. Reduced denominator and the Jacobsthal lift

Let \(D_n=2^{27n}L_{7n}\) be the raw denominator used by the exact
sevenfold recurrence, and write

\[
q10^nB_{7n}={U_{n,P}\over D_n}
\]

before reduction. The independently audited all-depth valuation gives

\[
v_2(U_{n,P})=v_2(7n+1).                              \tag{A11}
\]

Because \(q\) and \(5^n\) are odd, no additional two-primary cancellation
occurs. If \(Q_n=Q_{n,P}\) is the reduced denominator, then

\[
v_2(Q_n)=27n-v_2(7n+1).                             \tag{A12}
\]

The independently audited odd-denominator result gives

\[
\log R_{7n}=(42+o(1))n.
\]

Multiplication by fixed \(q\) removes only \(O_P(1)\) logarithmic mass.
Multiplication by \(5^n\) can remove only \(O(\log n)\), because the
5-primary exponent in an lcm of \(O(n)\)-sized factors is \(O(\log n)\).
Together with (A12),

\[
\log Q_n=(42+27\log2+o(1))n.                        \tag{A13}
\]

Every prime divisor comes from a linear factor of size \(O(n)\), apart from
the fixed multiplier, so the prime number theorem gives

\[
\omega(Q_n)=o(n).                                   \tag{A14}
\]

Use the audited Jacobsthal convention in which every interval of
\(j(M)\) consecutive integers contains an integer coprime to \(M\).
Kanold's bound is

\[
j(M)\leq2^{\omega(M)}.                              \tag{A15}
\]

Apply it to an interval adjacent to \(Q_nt_n\). There is an integer \(u_n\)
with

\[
(u_n,Q_n)=1,\qquad
\left|{u_n\over Q_n}-t_n\right|
\leq{2^{\omega(Q_n)}+1\over Q_n}.                   \tag{A16}
\]

Negative target values pose no issue because
\(\gcd(-u,Q_n)=\gcd(u,Q_n)\). Equations (A13)--(A14) turn the right side
into

\[
\exp\!\left(-(42+27\log2-o(1))n\right).             \tag{A17}
\]

This is exponentially smaller than \(|t_n|\), whose exponential rate in
(A9) is

\[
27\log2-\log5.                                      \tag{A18}
\]

Consequently

\[
\widetilde e_n={u_n\over Q_n}\in(-1/2,0)            \tag{A19}
\]

for every sufficiently large \(n\). Its reduced denominator is exactly
\(Q_n\), and choosing zero as its nearest integer gives zero centered carry.

## 4. Raw numerator valuation and pointwise forcing error

Set

\[
\widetilde S_n=D_n\widetilde e_n.
\]

Because \(Q_n\mid D_n\), this is an integer. Coprimality in (A16) and the
evenness of \(Q_n\) make \(u_n\) odd. Equations (A12) and (A19) therefore
give

\[
v_2(\widetilde S_n)
=v_2(D_n)-v_2(Q_n)
=v_2(7n+1).                                         \tag{A20}
\]

Thus the alternative phase has both the exact reduced denominator and the
exact selected raw two-adic order of the BBP phase.

Let

\[
\eta_n=\widetilde e_n-t_n,\qquad
\widetilde\delta_n=\widetilde e_{n+1}-10\widetilde e_n.           \tag{A21}
\]

Subtracting (A6) gives

\[
\widetilde\delta_n-\delta_n=\eta_{n+1}-10\eta_n.    \tag{A22}
\]

The right side has exponential rate at least
\(42+27\log2\), up to \(o(n)\), while (A10) has decay rate
\(27\log2-\log5\). Hence

\[
\left|{\widetilde\delta_n-\delta_n\over\delta_n}\right|
=O\!\left(
\exp\bigl(-(42+\log5-o(1))n\bigr)
\right).                                            \tag{A23}
\]

The exponent subtraction is

\[
(42+27\log2)-(27\log2-\log5)=42+\log5.              \tag{A24}
\]

It is positive, so \(\widetilde\delta_n>0\) eventually.

The integer recurrence also checks exactly. Since \(Q_n\mid D_n\),
\(Q_{n+1}\mid D_{n+1}\), and \(D_n\mid D_{n+1}\),

\[
\widetilde J_n=D_{n+1}\widetilde\delta_n\in\mathbb Z.
\]

Writing \(\Lambda_n=D_{n+1}/D_n\) gives

\[
\widetilde S_{n+1}
=10\Lambda_n\widetilde S_n+\widetilde J_n.          \tag{A25}
\]

Because every \(\widetilde e_n\) has nearest integer zero, all carries of
this modified phase/forcing system are zero.

The pointwise choices in (A16) are independent. Equation (A23) does not
assert that its numerator is nonzero at each \(n\). If equality
\(\widetilde\delta_n=\delta_n\) held from one final depth onward, however,
the rational bounded sequence would equal the irrational unique orbit (A5),
which is impossible. Infinitely many forcing differences are therefore
necessary. The second checker observed no finite coincidence on its tested
rows, but that bounded observation has label 'experiment'.

## 5. Coherent geometric resets

The pointwise system does not preserve exact BBP forcing on a specified
large set. To build a coherent version, choose a sufficiently large
power-of-two \(N_0\), put \(N_j=2^jN_0\), and use the exact-denominator
choice only at each reset \(N_j\). For \(N_j\leq n<N_{j+1}\), define

\[
\overline e_n=t_n+10^{n-N_j}\eta_{N_j}.             \tag{A26}
\]

Although both terms on the right involve pi, their irrational parts cancel:

\[
\overline e_n
=q10^n(B_{7n}-B_{7N_j})
+10^{n-N_j}{u_{N_j}\over Q_{N_j}},                  \tag{A27}
\]

which is rational. At a nonreset transition, (A6) gives

\[
\overline e_{n+1}=10\overline e_n+\delta_n.         \tag{A28}
\]

At the reset, \(\overline e_{N_j}=u_{N_j}/Q_{N_j}\).
Since \(Q_{N_j}\mid D_{N_j}\), the denominators \(D_n\) are nested, and
\(D_{n+1}\delta_n\) is integral, induction proves

\[
\operatorname{den}(\overline e_n)\mid D_n           \tag{A29}
\]

at every depth. Equality with \(Q_n\) is neither needed nor proved between
resets.

The reset perturbation stays uniformly small on a doubled block. From
(A17),

\[
\max_{N_j\leq n<N_{j+1}}
10^{n-N_j}|\eta_{N_j}|
\leq
\exp\!\left(
-(42+27\log2-\log10-o(1))N_j
\right)=o(1).                                       \tag{A30}
\]

Together with \(t_n\to0\), this puts all late \(\overline e_n\) in
\((-1/2,1/2)\). Choosing nearest integer zero again makes every carry zero.

Define

\[
\overline\delta_n=\overline e_{n+1}-10\overline e_n.
\]

Equation (A28) shows exact equality

\[
\overline\delta_n=\delta_n                           \tag{A31}
\]

unless \(n=N_{j+1}-1\). There are only \(O(\log N)\) such indices below
\(N\). At an exceptional transition,

\[
\overline\delta_n-\delta_n
=\eta_{N_{j+1}}-10^{N_{j+1}-N_j}\eta_{N_j}.         \tag{A32}
\]

The second term dominates the asymptotic upper bound. Since
\(n=2N_j-1\), division by (A10) yields a relative-error exponent per \(n\)
equal to

\[
\begin{aligned}
c_0
&={42+27\log2-\log10\over2}
 -(27\log2-\log5)\\
&=21-14\log2+{\log5\over2}
=12.1006584283\ldots>0.                             \tag{A33}
\end{aligned}
\]

Thus even the exceptional forcing is positive and exponentially
relative-close eventually. The forcing equals BBP on a density-one set, yet
the modified carry density is zero.

The resets cannot stop after finitely many stages. Otherwise (A31) would
hold forever, and boundedness plus uniqueness of (A5) would make a rational
phase irrational. Geometric resets show that only \(O(\log N)\) changes up
to depth \(N\) are sufficient to avoid this contradiction.

## 6. Height product and finite-difference scope

Suppose the actual rational BBP phase contains disjoint zero-carry blocks
starting at \(n_i\), with lengths \(h_i\). Its nonzero centered phase has
reduced denominator \(Q_{n_i}\), hence

\[
|e_{n_i}|\geq Q_{n_i}^{-1}.                          \tag{A34}
\]

The exact block recurrence and BBP tail give

\[
|e_{n_i}|
\leq{1\over2\,10^{h_i}}
+{q5^{n_i}\over2^{27n_i}15(7n_i+1)^2}.              \tag{A35}
\]

The published irrationality-measure range keeps \(h_i\) below a constant
strictly smaller than
\((27\log2-\log5)n_i/\log10\). Therefore the tail term in (A35) is
eventually smaller than the first. Taking logarithms and summing yields only

\[
(\log10)\sum_{i=1}^Kh_i
\leq(42+27\log2+o(1))\sum_{i=1}^Kn_i+O_P(K).        \tag{A36}
\]

Even if the blocks cover almost all indices below \(N\),
\(\sum_i n_i\) can be \(O(KN)\). Thus (A36) permits \(K=o(N)\), including
geometrically spaced resets. Nested raw denominators do not remove the
factor \(K\): a product of \(K\) nonzero rationals with denominator dividing
\(D_N\) is bounded below only by \(D_N^{-K}\).

Equivalently,

\[
\mathcal P_K(X)=\prod_{i=1}^K(q10^{n_i}X-z_{n_i})    \tag{A37}
\]

has degree \(K\) and logarithmic height
\(O_P(K+\sum_i n_i)\). Its small value at pi has exponent controlled by
\(\sum_i h_i\), so there is no generic favorable degree-height balance.
This does not exclude a new algebraic identity producing a genuinely shared
factor.

The coherent separator also survives every fixed number of shifts or finite
differences away from only a constant-width enlargement of its
\(O(\log N)\) reset set. Hence fixed-order identities, finite asymptotic
jets, signs, and raw-denominator divisibility alone cannot force positive
Cesaro carry density. An argument coupling exact reduced denominators to the
exact selected forcing at every depth is outside this separator.

## 7. Second independent replay

The second checker does not import the primary checker or the first
independent checker. It uses integer arithmetic and Python Fraction. It:

- pins eight canonical, primary, denominator-audit, Jacobsthal-audit, and
  BBP-source artifacts;
- rebuilds the BBP endpoints independently through sevenfold depth 960;
- checks 306 symbolic instances of the exact irrational zero-orbit
  recurrence;
- uses a farther BBP partial sum plus the rigorous positive tail bound to
  enclose each irrational target phase;
- independently performs the coprime-nearby search and checks its distance
  against \(2^{\omega(Q_n)}\);
- checks 309 exact-denominator states and 306 integer zero-carry recurrences
  for the distinct periods \(P=1,3,5\);
- checks coherent systems through depth 208 with reset predecessors
  \(47,95,191\), including every exact/nonexact transition and raw-denominator
  divisibility; and
- explicitly records that the coherent system's reduced denominator differs
  from \(Q_n\) at 143 or 144 of the 185 checked states, preventing accidental
  conflation of the two separator bundles.

Replay:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_second_independent_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_second_independent_check.py

The retained run reports 'status: PASS',
'asserts_positive_carry_density: false', and 'asserts_v1: false'. It computes
\(42+\log5=43.6094379124\ldots\) and
\(c_0=12.1006584283\ldots\), and its maximum reset relative error is below
\(10^{-249}\) on all three tested periods. These rows have label
'experiment'.

## Final claim audit

The primary separator is mathematically supported with status
'proof sketch', subject to the two scope clarifications in the verdict.
It establishes no result about the actual frequency of pi's carries. In
particular:

- the unique irrational orbit proves only infinitely many departures for a
  rational phase, not positive density;
- the alternative pointwise phases intentionally change the selected
  numerators;
- the coherent phase intentionally resets and does not retain exact
  \(Q_{n,P}\) between resets;
- finite replay supplies no asymptotic theorem; and
- neither construction proves decimal disjunctivity or V1.

The correct surviving target is the exact cross-depth selected-numerator
correlation of the actual BBP phase. No estimate for that correlation is
proved here. Canonical V1 remains a 'conjecture'.
