# Independent audit: BBP scalar p-adic/Archimedean separator

Audit date: **2026-08-13 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target has no external source URL; none is invented.

Audited frozen artifacts:

- [`bbp_scalar_padic_archimedean_separator_20260813.md`](bbp_scalar_padic_archimedean_separator_20260813.md),
  SHA-256
  `ce581bf5bb9c1b95d2405c27839bd6e894e90dda8d0a8c1808e1b722e059a357`;
- [`bbp_scalar_padic_archimedean_separator_20260813_check.py`](bbp_scalar_padic_archimedean_separator_20260813_check.py),
  SHA-256
  `5c75450eda7f1998136a7e7583bb5c8925a791dfd8d1af4f76a57f94ec323350`.

Independent replay:

- [`bbp_scalar_padic_archimedean_separator_independent_check_20260813.py`](bbp_scalar_padic_archimedean_separator_independent_check_20260813.py),
  SHA-256
  `b77c84b6e8d5ab54be930bde4cc94a76750664a6c1dc668ebde48d8a0eadd9d6`.

## Verdict

**PASS, with no mathematical correction required.**

The four-pole coefficients, endpoint splice, all signs, uniform gap, exact
two-adic phase order, two-scale forcing coefficients, and arbitrary-fixed-jet
Kanold lift all rederive.  In particular, the following data genuinely
coexist in one spliced rational phase sequence:

1. an integral initial phase and the exact actual values \(h_0,h_1\);
2. from some freely chosen finite depth onward, the complete actual reduced
   denominator of \(B_n\) and every bit of the two-adic congruence derived in
   the all-depth report;
3. any prescribed **fixed finite** Laurent jet at both the \((5/8)^n\) and
   \(16^{-n}\) forcing scales;
4. eventual negative scalar forcing; and
5. circle distance tending to \(1/3\), hence nonreturn.

Two scope qualifications are load-bearing and are already stated correctly
in the frozen report.  The complete-denominator/two-adic assertions are only
eventual; the finite anchor splice is not claimed to retain them.  Also the
lifted values are selected independently at each depth.  They are not claimed
to satisfy the exact cross-depth BBP partial-sum increment.  Thus this is a
method separator, not a counterexample involving pi.

The analytic statements remain `proof sketch`; the bounded source check is
`literature-checked` on the displayed date; every finite replay is an
`experiment`.  Nothing in this audit is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.  No return theorem is
proved.  Canonical V1 remains a `conjecture`.

## 1. Exact scalar recurrence and actual sign

Put

\[
 D(k)=(2k+1)(4k+3)(8k+1)(8k+5),\qquad
 a(k)={120k^2+151k+47\over D(k)},
\]

\[
 b_k={a(k)\over16^k},\qquad B_n=\sum_{k=0}^n b_k,
 \qquad q_n=10^n-16,\qquad R_n=q_nB_n.
\]

Using \(B_{n+1}=B_n+b_{n+1}\), direct cancellation of the \(B_n\)
coefficient gives

\[
\begin{aligned}
 R_{n+2}-11R_{n+1}+10R_n
  &=(10^{n+2}-16)b_{n+2}
    +(160-10^{n+1})b_{n+1}\\
  &=h_n.
\end{aligned}                                      \tag{A1}
\]

An independent polynomial subtraction gives

\[
 a(k)-a(k+1)
 ={3P(k)\over D(k)D(k+1)},
\]

where

\[
 P(k)=40960k^5+220672k^4+453632k^3+443480k^2
      +206712k+36903.
\]

All coefficients are positive, so \(0<b_{k+1}<b_k/16\).  Exact endpoint
reduction gives

\[
 h_0={20048317\over16336320}>0,\qquad
 h_1={258249\over17353600}>0.
\]

For \(n\ge2\), (A1) and the strict coefficient decrease give

\[
 h_n<\left({10^{n+2}-16\over16}+160-10^{n+1}\right)b_{n+1}
     =\left(159-{3\over8}10^{n+1}\right)b_{n+1}<0. \tag{A2}
\]

Thus the actual sign change is exactly where the report places it.

If \(T_n=\pi-B_n\), \(E_n=q_nT_n\), and

\[
 (Lx)_n=11x_{n+1}-10x_n-x_{n+2},
\]

then \(q_n\pi\) is killed by the complementary recurrence and (A1) yields

\[
 h_n=(LE)_n.                                        \tag{A3}
\]

No distribution assertion enters these identities.

## 2. Full tail coordinate and its rational jets

Let \(\rho=5/8\), \(\sigma=1/16\), and

\[
 G_n=15\sum_{j\ge1}{a(n+j)\over16^j}.
\]

Index shifting gives the exact identities

\[
 T_n={16^{-n}\over15}G_n,\qquad
 E_n={\rho^n-16\sigma^n\over15}G_n.                \tag{A4}
\]

Expansion at infinity gives

\[
 a(n)={15\over64n^2}-{89\over512n^3}+O(n^{-4}).
\]

The exact moments

\[
 \mu_r=15\sum_{j\ge1}{j^r\over16^j}
\]

are rational for every fixed \(r\), with
\(\mu_0=1\) and \(\mu_1=16/15\).  Therefore

\[
 G_n={15\over64n^2}-{345\over512n^3}+O(n^{-4}).    \tag{A5}
\]

The claimed explicit proxy

\[
 g(n)={15(n+1)(8n-15)\over D(n)}
\]

has exactly the same first two coefficients.  This follows either by direct
division or by observing that its numerator is
\(120n^2-105n-225\):

\[
 g(n)={15\over64n^2}-{345\over512n^3}+O(n^{-4}).   \tag{A6}
\]

The arbitrary-jet assertion also rederives.  If

\[
 a(x)\sim\sum_{r\ge2}A_rx^{-r},
\]

then the coefficient of \(n^{-s}\) in \(G_n\) is

\[
 c_s=\sum_{r=2}^s A_r(-1)^{s-r}
          {s-1\choose r-1}\mu_{s-r}\in\mathbb Q.  \tag{A7}
\]

For each fixed \(J\ge2\), set

\[
 g_J(n)=\sum_{r=2}^Jc_rn^{-r}.
\]

Taylor expansion for \(j\le n\), followed by the geometric tail for
\(j>n\), proves

\[
 G_n-g_J(n)=O(n^{-J-1}).                            \tag{A8}
\]

The remainder is uniform under the \(16^{-j}\) sum because each fixed-order
remainder is bounded by a polynomial in \(j\), and all such moments converge.
The independent checker reconstructed (A7), rather than copying coefficients,
through \(J=10\).

## 3. Endpoint splice, sign, and uniform nonreturn

For \(n\ge3\), put

\[
 \varepsilon_n={\rho^n-16\sigma^n\over15}g(n)
               ={q_ng(n)\over15\,16^n}.
\]

Set \(\varepsilon_0=1/3\), and solve

\[
 11\varepsilon_1-10\varepsilon_0-\varepsilon_2=h_0,
 \qquad
 11\varepsilon_2-10\varepsilon_1-\varepsilon_3=h_1.
\]

The determinant is \(111\), so the solution is unique.  Independent exact
reduction gives

\[
 \varepsilon_1={3095504003\over6847215375},\qquad
 \varepsilon_2={25814204941\over62603112000}.       \tag{A9}
\]

Define

\[
 R_n^*={q_n\over9}-\varepsilon_n,
 \qquad
 h_n^*=R_{n+2}^*-11R_{n+1}^*+10R_n^*.
\]

Because \(q_n/9\) is homogeneous,

\[
 h_n^*=11\varepsilon_{n+1}-10\varepsilon_n-\varepsilon_{n+2}. \tag{A10}
\]

Equations (A9)--(A10) give \(R_0^*=-2\),
\(h_0^*=h_0\), \(h_1^*=h_1\), and

\[
 h_2^*=-{411876045113669\over99914566752000}<0.    \tag{A11}
\]

For the tail sign, exact common-denominator subtraction gives

\[
 g(n)-g(n+1)={15P_g(n)\over D(n)D(n+1)},
\]

\[
 P_g(n)=8192n^5+17920n^4-33792n^3-122248n^2
        -115688n-36645.
\]

After \(n=m+3\), this becomes

\[
 8192m^5+140800m^4+918528m^3+2753144m^2
 +3491560m+1045851,
\]

which is positive for \(m\ge0\).  Hence \(g\) is positive and strictly
decreasing for \(n\ge3\).  Also, for \(n\ge2\), direct cross multiplication
shows

\[
 {q_{n+1}\over16q_n}<{10\over11}
 \quad\Longleftrightarrow\quad
 50\,10^n>2384.
\]

It follows that
\(\varepsilon_{n+1}/\varepsilon_n<10/11\) for \(n\ge3\), and hence

\[
 h_n^*<-\varepsilon_{n+2}<0\qquad(n\ge3).          \tag{A12}
\]

Together with (A11), this is exactly the claimed sign pattern.

The gap is also exact.  Since \(q_n/9\equiv1/3\pmod1\), the two exceptional
increments are

\[
 \varepsilon_1-{1\over3}={813098878\over6847215375},\qquad
 \varepsilon_2-{1\over3}={1648833647\over20867704000},
\]

and each lies strictly between \(1/16\) and \(1/2\).  For \(n\ge3\),
\(0<g(n)<n^{-2}\): after multiplication by the positive denominator, the
second inequality has difference

\[
 D(n)-15n^2(n+1)(8n-15)
 =392n^4+1129n^3+937n^2+194n+15>0.
\]

Consequently

\[
 0<\varepsilon_n<{\rho^n\over15n^2}<{1\over24}.
\]

Taking the nearest representative in each case proves

\[
 \boxed{\|R_n^*\|_{\mathbb T}>1/16\quad(n\ge1).}   \tag{A13}
\]

No finite check is being promoted to this all-index proof.

## 4. Exact two-primary phase order

The all-depth dependency proves

\[
 v_2(B_n)=v_2(n+1)-4n.                              \tag{A14}
\]

For \(n\ge3\), the separator can be written

\[
 R_n^*=q_n\left({1\over9}
 -{(n+1)(8n-15)\over D(n)16^n}\right).
\]

The bracket numerator over \(9D(n)16^n\) is

\[
 D(n)16^n-9(n+1)(8n-15).                           \tag{A15}
\]

Its summands have unequal two-adic valuations \(4n\) and \(v_2(n+1)\).
Therefore

\[
 v_2(R_n^*)=v_2(q_n)+v_2(n+1)-4n=v_2(q_nB_n).      \tag{A16}
\]

For \(n=3,4\) the values \(v_2(q_n)\) are \(3,8\), while
\(v_2(q_n)=4\) for \(n\ge5\).  Thus both sides of (A16) are negative, and
(A16) really is equality of the exact two-primary denominator orders of the
two rational phases, not merely equality of valuations in an integral case.

## 5. Both Archimedean forcing scales

Equations (A4), (A6), and the finite operator \(L\) give

\[
 h_n-h_n^*=O(\rho^nn^{-4})+O(\sigma^nn^{-4}).       \tag{A17}
\]

For a term \(\alpha\lambda^n c_2n^{-2}\), the leading multiplier under \(L\)
is

\[
 \alpha c_2(11\lambda-10-\lambda^2).
\]

Using \(c_2=15/64\), \(\alpha=1/15\) at \(\lambda=5/8\), and
\(\alpha=-16/15\) at \(\lambda=1/16\), this yields

\[
 h_n^{(\rho)}\sim-{225\over4096}{\rho^n\over n^2},
 \qquad
 h_n^{(\sigma)}\sim {2385\over1024}{\sigma^n\over n^2}. \tag{A18}
\]

Thus the sign of the dominant scale is genuinely negative, and the two
leading terms at each scale agree for the explicit four-pole proxy.

More generally, (A8) gives

\[
 L\!\left({\rho^n-16\sigma^n\over15}(G_n-g_J(n))\right)
 =O(\rho^nn^{-J-1})+O(\sigma^nn^{-J-1}).            \tag{A19}
\]

This is the exact finite-jet statement used below.

## 6. Independent derivation of the Kanold lift

Write the actual reduced partial sum as

\[
 B_n={P_n\over2^{K_n}O_n},\qquad
 K_n=4n-v_2(n+1),\qquad (P_n,2O_n)=1,              \tag{A20}
\]

where \(O_n\) is odd.  The audited odd-denominator dependency proves

\[
 \log O_n=(6+o(1))n,\qquad \omega(O_n)=o(n).        \tag{A21}
\]

The lift can be seen without importing the primary checker's complementary
quotient code.  Given any real target \(\beta_n\), put

\[
 T_n={O_n(\beta_n-B_n)\over16}.
\]

Because \(2^{K_n+4}\) is a unit modulo \(O_n\), the condition

\[
 (P_n+2^{K_n+4}t,O_n)=1
\]

is a translate, in the integer \(t\), of ordinary coprimality to \(O_n\).
Kanold's bound \(j(O_n)\le2^{\omega(O_n)}\) therefore supplies an integer
\(t_n\) with

\[
 |t_n-T_n|=O(2^{\omega(O_n)}),\qquad
 (P_n+2^{K_n+4}t_n,O_n)=1.                         \tag{A22}
\]

Define

\[
 \widehat B_n={P_n+2^{K_n+4}t_n\over2^{K_n}O_n}
              =B_n+{16t_n\over O_n}.               \tag{A23}
\]

The numerator in (A23) remains odd and is a unit modulo \(O_n\), so the
complete reduced denominator \(2^{K_n}O_n\) is unchanged.  Moreover,

\[
 (P_n+2^{K_n+4}t_n)O_n^{-1}
 \equiv P_nO_n^{-1}\pmod {2^{K_n+4}},              \tag{A24}
\]

and

\[
 v_2\!\left(16^n(\widehat B_n-B_n)\right)
 \ge4(n+1).                                        \tag{A25}
\]

The modulus \(2^{K_n+4}=256\cdot2^{K_n-4}\) is exactly the complete
two-adic precision derived by the all-depth null identity.  Hence (A24)--(A25)
preserve **all two-adic bits derived there**.  They do not preserve the odd
numerator coordinate modulo \(O_n\), which is the intended degree of freedom.

Finally, (A22)--(A23) give, pointwise for the varying target sequence,

\[
 |\widehat B_n-\beta_n|
 =O\!\left({2^{\omega(O_n)}\over O_n}\right)
 =\exp((-6+o(1))n).                                \tag{A26}
\]

This proves that the lift is not restricted to a constant target and does
not require nested odd denominators.

## 7. Arbitrary fixed jet, denominator data, and nonreturn coexist

Fix any \(J\ge2\), and define

\[
 \bar\varepsilon_n^{(J)}
 ={\rho^n-16\sigma^n\over15}g_J(n),\qquad
 \beta_n={1\over9}-{\bar\varepsilon_n^{(J)}\over q_n}. \tag{A27}
\]

Then

\[
 q_n\beta_n={q_n\over9}-\bar\varepsilon_n^{(J)}.
\]

Apply (A26) independently at every sufficiently large depth and put
\(\widehat R_n=q_n\widehat B_n\).  Since

\[
 6-\log10>\log16,
\]

one obtains, for every fixed \(A\),

\[
 |\widehat R_n-q_n\beta_n|
 =\exp(-(6-\log10+o(1))n)
 =o(16^{-n}n^{-A}).                                \tag{A28}
\]

Applying the three-term scalar operator to (A28) preserves the estimate.
Combining it with (A19) proves agreement with the actual \(h_n\) through
the prescribed \(J\)-term jet at both scales.  By (A18), the lifted forcing
is negative for every sufficiently large \(n\).

On the other hand, \(q_n/9\equiv1/3\pmod1\),
\(\bar\varepsilon_n^{(J)}\to0\), and the lift error in (A28) tends to zero.
Consequently

\[
 \boxed{\|\widehat R_n\|_{\mathbb T}\longrightarrow1/3.} \tag{A29}
\]

Equations (A20), (A24), (A28), and (A29) prove the claimed simultaneous
complete-denominator, derived-two-adic, arbitrary-fixed-jet, and nonreturn
properties.

To add the initial anchor, choose a large \(N\), use \(R_n^*\) for \(n<N\)
(in particular through \(R_3^*\)), and use \(\widehat R_n\) for \(n\ge N\).
Then \(R_0^*=-2\) and \(h_0,h_1\) are exact.  The two forcing rows straddling
the splice are unconstrained; all denominator and two-adic assertions start
at \(N\); and eventual forcing is negative.  These are exactly the frozen
report's qualifications.

The resulting values do not obey the exact BBP increment
\(B_{n+1}-B_n=b_{n+1}\).  Therefore the separator rules out deductions from
the retained data alone; it does not rule out an argument using the actual
cross-depth odd numerators or the exact four-pole correlation.

## 8. Dependency and source audit

All hashes pinned by the frozen checker matched.  The independent checker
also pins the frozen report, its checker, every load-bearing audited local
dependency, and the Bailey--Crandall source directly: 14 artifacts in total.

The source boundaries and locators are correct.

- Bailey--Borwein--Plouffe supplies the four-pole base-16 series, not decimal
  normality or the return (A29).  Local SHA-256:
  `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`.
- Lagarias describes the BBP/G-function dynamics and explicitly treats the
  relevant distribution conclusion through the unproved Hypothesis A.
  Local SHA-256:
  `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9`.
- Bailey--Crandall states Hypothesis A and conditional normality consequences;
  it does not prove the coefficient-specific return here.  Local SHA-256:
  `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8`.
- Kanold, [*Über eine zahlentheoretische Funktion von
  Jacobsthal*](https://eudml.org/doc/161543), Math. Ann. 170 (1967),
  314--326, Satz 4 on printed p. 324, supplies
  \(j(m)\le2^{\omega(m)}\).  The official GDZ scan was independently
  refetched during this audit and had SHA-256
  `dd75cd1ff949feff49b0e7ca9ca2379518e8f65e075ee99a7df4f247c80c97cb`,
  exactly matching the prior source audit.  Coprimality depends only on the
  radical, so the prime-power content of \(O_n\) causes no applicability gap.

The denominator asymptotic and all-depth two-adic identity are not silently
reproved from finite output: they are explicitly inherited from the pinned,
independently audited dependency reports.  The present audit independently
checks that their exact statements are sufficient for (A20)--(A29).

## 9. Independent replay

The independent checker imports no primary checker.  It reconstructs:

- the Laurent coefficients and rational geometric moments;
- the all-positive polynomial proving \(a(k)>a(k+1)\);
- the shifted all-positive polynomial proving \(g(n)>g(n+1)\);
- the endpoint system, exact splice fractions, \(h_2^*\), and all recurrences;
- the uniform gap and exact phase valuations;
- both leading forcing coefficients and generic jets through the requested
  finite order;
- the lift by modifying the reduced numerator directly by
  \(2^{K_n+4}t\), rather than importing the primary complementary-quotient
  implementation;
- complete denominator preservation, the full derived two-adic residue,
  varying-target finite lifts, and one concrete endpoint/tail splice.

Run:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_independent_check_20260813.py
.venv/bin/python \
  work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_independent_check_20260813.py \
  --max-depth 84 --lift-depth 58 --max-jet 8
```

Retained output:

```text
status: PASS
claim_label: experiment
pinned_artifacts: 14
c0_scanned_text_artifacts: 12
generic_tail_jet_orders_checked: 2..8
tail_jet_coefficients_through_8: 15/64,-345/512,6225/4096,-106365/32768,1858065/262144,-34815045/2097152,721379625/16777216
exact_scalar_checks: 85
valuation_checks: 164
uniform_gap_checks: 84
varying_target_full_denominator_lift_checks: 1785
maximum_lift_center_offset: 9
maximum_finite_offset_over_2powomega: 0.000183105469
minimum_finite_lifted_circle_gap: 0.333327648989
finite_splice_eventual_negative_rows: 41
matched_actual_endpoint_forcing: h_0,h_1
uniform_unlifted_gap_lower_bound: 1/16
asserts_fixed_return: false
asserts_v1: false
all independent exact finite checks passed
```

A separate deeper run through depth 110, lift depth 84, and jet order 10 also
passed.  These finite rows remain an `experiment`.

## Sharp conclusion

The frozen no-go is sound within its stated scope.  Exact \(2\)-primary
phase order, the full currently derived two-adic coordinate, the complete
actual denominator, endpoint anchoring, eventual one-sided forcing, and any
one fixed finite two-scale asymptotic jet do not force the accumulated phase
to return to zero.

What the construction changes is exactly the odd numerator coordinate at
each depth and its cross-depth BBP coherence.  A successful scalar proof must
therefore use information of that kind—for example, a nontrivial
coefficient-specific exponential-sum estimate or an exact four-pole
correlation.  The audit supplies no such estimate, so V1 remains a
`conjecture`.
