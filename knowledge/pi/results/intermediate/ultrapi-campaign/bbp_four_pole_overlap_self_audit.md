# Adversarial self-audit of the BBP four-pole overlap obstruction

Audit date: **2026-08-12 UTC**

Target: [`bbp_four_pole_overlap_attack.md`](bbp_four_pole_overlap_attack.md)

Corrected target SHA-256:
`9d9ff606cf0de438061e2a9245d0f0d3fc1cbfb784b1ca6be6aac76195a13545`

Corrected primary checker SHA-256:
`418191b0e515a724c9bb51fb3c0853e27884fa0b155f68487831aa703168e750`

Canonical question SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict and claim labels

**PASS after corrections.**  A second derivation found no error in the
four-pole coefficient, the tail estimate, the constant
\(272\pi|q|/(45N)\), the recurrence indices, or the frequency-ray and
fixed-point obstructions.  It did find several boundary and scope statements
that were too implicit, plus one imprecise finite-\(M\) stationarity sentence.
Those are corrected in the pinned target above.

This is deliberately a self-audit, not an independent review.  The
mathematical derivations retain claim label `proof sketch`; the deterministic
checker is an `experiment`; and the dated source search in the target is
`literature-checked`.  Only the cited pre-existing T25 dependency is
`machine-checked`.  Nothing here is a `candidate resolution` or a `verified
resolution`, and neither T70 overlap nor V1 is proved.

## Corrections made

The initial report had SHA-256
`ccfa800568628f498df788dee2a355ef92dc26230e9c99da65b755b1276e01f9`;
the initial checker had SHA-256
`a546efa38adef4eb85958d2ccc94accc037199f3536354cc5cca6e3d68f18ecb`.
The audit made these inspectable corrections:

1. It now says explicitly that \(D_N\) requires \(N\ge1\), that \(N=0\) is
   undefined, and that \(q=0\) gives the identically zero target.  Every
   subsequence is stated to have \(N_j\to\infty\).
2. The rational finite surrogate is indexed as \(0\le n\le M\), with its
   recurrence restricted to \(0\le n<M\).  This removes the former ambiguity
   at \(t_{M,M}=0\); the formula itself was correct.
3. The Dirac three-cycle average is now described as exactly stationary when
   \(3\mid M\), and merely asymptotically stationary for arbitrary
   \(M\to\infty\).  Exact stationarity for every finite \(M\) would be false.
4. The sparse-digit exceptional count is now the directly justified
   \(L(1+\lfloor\log_2(N+L)\rfloor)\), matching the checker, rather than the
   looser-looking but unproved expression with \(N\) alone.  Either form has
   the required \(O_L(\log N)\) asymptotic, but the corrected one follows
   immediately by counting all relevant powers of two.
5. The claim-label paragraph now distinguishes new `proof sketch` results,
   the checker `experiment`, the `literature-checked` search, and the existing
   `machine-checked` T25 dependency.  The former sentence “nothing here is
   machine-checked” was inconsistent with the later T25 citation.
6. The replay inventory now lists the pinned fixed-return report and audit,
   and the handoff limits its warning about asymptotic stationarity to the
   universal-uniform and Cesaro-only classes actually excluded.

None of these corrections changes the main negative conclusion: the BBP
forcing is erased at Cesaro scale and supplies no proved \(q\)-to-\(16q\)
bridge.

## Independent rederivation of the constants

For \(k\ge0\), exact common-denominator expansion gives

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}>0.
\]

For \(k\ge1\), subtracting this from \(1/k^2\) has numerator

\[
 392k^4+873k^3+665k^2+194k+15,
\]

whose coefficients are all positive.  Therefore

\[
\begin{aligned}
t_n
 &=10^n\sum_{k=n+1}^{\infty}\frac{a(k)}{16^k}\\
 &\le \frac{10^n}{(n+1)^2}
       \sum_{k=n+1}^{\infty}16^{-k}\\
 &=\frac{(5/8)^n}{15(n+1)^2}.
\end{aligned}
\]

The index \(k=n+1\) is essential: it makes the elementary bound valid even
at \(n=0\).  Dropping \((n+1)^{-2}\le1\) and summing gives

\[
 \sum_{n\ge0}t_n
 \le \frac1{15}\sum_{n\ge0}(5/8)^n
 =\frac1{15}\frac1{1-5/8}=\frac8{45}.
\]

For a circle character, the two frequencies in the defect have Lipschitz
constants \(2\pi|16q|\) and \(2\pi|q|\).  Hence the multiplier is
\(2(16+1)=34\), not 32 or 17, and

\[
 \frac{34\pi|q|}{N}\frac8{45}
 =\frac{272\pi|q|}{45N}.
\]

The absolute value handles negative \(q\); for \(q=0\) both sides are zero.
Division requires \(N\ge1\).  Thus the constant and every boundary in the
main \(O_q(N^{-1})\) estimate survive the adversarial pass.

## Equation-by-equation audit

| Equation | Audit result |
|---|---|
| (1) | Correct for every \(q\in\mathbb Z\) and \(N\ge1\); at \(q=0\) it is \(0\le0\). |
| (2) | Symbolically cross-multiplied; numerator \(120k^2+151k+47\) and all four denominator factors are correct. |
| (3) | The inclusive partial sum \(0\le k\le n\) produces \(u_0=\{a(0)\}\) and the recurrence at \(n=0\). |
| (4) | Correct from the positive BBP tail and \(a(k)<1/k^2\) for \(k\ge1\); no unproved decimal approximation is used. |
| (5) | Correct geometric relaxation, exactly \(8/45\). |
| (6) | Correct same-time defect definition for \(N\ge1\).  \(N=0\) is undefined and \(q=0\) is trivial. |
| (7) | Correct stronger target.  Along a convergent empirical subsequence, all integer Fourier equalities imply equality of circle probabilities. |
| (8) | Correct triangle inequality and constant \(34\cdot8/45=272/45\). |
| (9) | Correct along the full sequence or any common \(N_j\to\infty\), because the difference is \(O_q(1/N_j)\). |
| (10) | Correct for \(0\le n<M\): both sides reduce to \(10^{n+1}(B_{n+1}-B_n)\). |
| (11) | Correct since \(10^{n+1}/16^{n+1}=(5/8)^{n+1}\). |
| (12) | Correct modulo one for every integer \(m\), including negative \(m\) and \(m=0\). |
| (13) | Correct sign: \(Z_n(10m)=e(-m\epsilon_{n+1})Z_{n+1}(m)\).  The identity also holds for the empty sum \(N=0\). |
| (14) | Symbolic numerator checked as \((15,194,665,873,392)\) in ascending degree; positivity is immediate for \(n\ge1\). |
| (15) | Correct frequency transfer \(m\mapsto10m\); the scalar phase never changes the ray. |
| (16) | Each finite Fourier term contributes opposite coefficients on one ten-ray; constants cancel as well. |
| (17) | At \(q=0\) it is zero.  For \(q\ne0\), its two frequencies are distinct. |
| (18) | Correct for trigonometric-polynomial stationary transfer functions and \(q\ne0\); it is not a statement about orbit-only identities. |
| (19) | Correct: equality at \(1/9\) is equivalent to \(5q/3\in\mathbb Z\), hence \(3\mid q\). |
| (20) | Correct only under all three stated hypotheses: a universal identity in \(x\), \(\psi_n\to\psi\) uniformly, and \(r_n\to0\) uniformly. |
| (21) | Correct: a rational \(R(k)\) grows at most polynomially, so its \(16^{-k}\) boundary vanishes and would make pi rational. |
| (22) | Correct induction; the exponent on 10 is \(h-j\), while the perturbation index is \(n+j\). |
| (23) | Correct for \(n\ge0,h\ge1\), using \((n+j)^{-2}\le(n+1)^{-2}\). |
| (24) | Exact signed-measure endpoint identity for \(M\ge1\); it makes limits invariant but says nothing about adjacent overlap. |
| (25) | Correct cycle \(1/9\mapsto7/9\mapsto4/9\mapsto1/9\); exact finite stationarity occurs precisely when \(3\mid M\). |

## Scope of the four different obstructions

These results must not be merged into a broader impossibility statement.

- **Finite Fourier:** for \(q\ne0\), the ray signature excludes
  \(\phi_q=\psi\circ T_{10}-\psi\) when \(\psi\) is a trigonometric
  polynomial.
- **Stationary continuous:** the fixed point \(1/9\) excludes any continuous
  stationary \(\psi\) when \(3\nmid q\).  Only \(q=1\) is needed for the
  proposed all-frequency target.  This particular point gives no obstruction
  when \(3\mid q\).
- **Uniformly asymptotically stationary:** the limit argument excludes only
  universal identities holding for every circle point with
  \(\psi_n\to\psi\) and \(r_n\to0\) uniformly.  It does not exclude pointwise
  convergence, unstable transfer functions, or an identity defined only on
  the selected BBP orbit.
- **Cesaro-only:** averaging \(S^t\mu\) produces asymptotic stationarity by an
  endpoint identity, but the Dirac cycle shows that this alone does not force
  \(\mu\) and \(S\mu\) to overlap.  This is a logical separator, not a model
  of the actual BBP coefficient.

Likewise, the fixed-lag calculation finds no zero-frequency term in the
first van-der-Corput expansion.  It does **not** exclude a future proof based
on new estimates for the resulting nonzero-frequency sums.

## Second exact checker

The companion
[`bbp_four_pole_overlap_self_audit_check.py`](bbp_four_pole_overlap_self_audit_check.py)
has SHA-256
`9b2dde3acb182cd5e31282aa3673ea45a7e09c6028a7fe3e2a4a21924479ab9c`.
It is a separate implementation and does not import the primary checker.  It
performs symbolic polynomial checks and 9,661 deterministic exact checks,
many on fixed-seed randomized inputs, including:

- positive, negative, and zero frequencies;
- \(N=0\) as a valid empty telescope but an invalid normalized average;
- randomized recurrence, finite-tail, fixed-lag, and phase identities;
- the Fourier telescope in the exact group ring of rational circle phases,
  without floating-point exponentials;
- random finite Fourier polynomials and ten-ray signatures;
- all \(-2000\le q\le2000\) fixed-point divisibility cases;
- random finite-state versions of the Cesaro endpoint identity; and
- random sparse-window exceptional counts using the corrected safe bound.

Replay both checkers from the repository root:

```bash
python work/ultrapi-resume/bbp_four_pole_overlap_check.py
python work/ultrapi-resume/bbp_four_pole_overlap_self_audit_check.py
```

Both return `PASS` while explicitly setting `asserts_overlap`,
`asserts_fourier_limit`, and `asserts_v1` to false.  A genuinely independent
auditor is still required before treating this self-audit as external
confirmation.
