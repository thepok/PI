# Independent audit: BBP fixed-period carries and the logarithmic barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is the local human-authored question; no external source URL is
invented.

## Verdict

**PASS**, with the exact claim boundary stated by the primary report.

The modular BBP identities, the bounded total transfer from the diagonal BBP
row to the true decimal orbit, the centered-carry/energy equivalence, the
sevenfold eventual rational coding, the logarithmic lower bound, and the
Kempner--Fredholm separator all re-derive correctly. The assembled result is
a `proof sketch`; the finite computations are an `experiment`; and the
bounded source audit is `literature-checked` on the date above.

This is not a positive Cesaro-defect theorem. It proves neither the adjacent
matching premise nor a fixed-sixteen return. In particular, it does not prove
that any nonempty decimal word occurs in pi, let alone every word. Canonical
V1 remains a `conjecture`. Nothing in this audit is a `candidate resolution`
or a `verified resolution`.

## Frozen inputs and the caught refreeze

The initially assigned expected hashes did not match the files on disk:

| artifact | initially supplied hash | observed hash |
|---|---|---|
| primary report | `bab423ed425c4407972b6eadccd830c2acff336282124d989407b2115c62a610` | `bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55` |
| primary checker | `9a79401a2b9d5bdd7431d0026faafa56df39e60f59b83e090434a8914e7ca77d` | `48a9db36d577376b0229f48c37ae399cdebe62d1a9c0c2959bebd368a4fe9ceb` |

The audit paused rather than silently accepting mutable inputs. The research
coordinator then confirmed that the observed versions include the intended
sevenfold-oversampling addition, stopped further edits, and explicitly
refroze those two observed hashes. This audit uses only the refrozen pair:

- [primary report](bbp_fixed_period_carry_attack_20260813.md), SHA-256
  `bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55`;
- [primary checker](bbp_fixed_period_carry_attack_20260813_check.py), SHA-256
  `48a9db36d577376b0229f48c37ae399cdebe62d1a9c0c2959bebd368a4fe9ceb`.

Both remained unchanged throughout the completed audit.

## 1. Target and quantifier audit

The primary normalization of V1 is exact:

\[
 \forall m\geq0\ \forall w\in\{0,\ldots,9\}^m\ \exists n\geq0\
 \ \forall i<m:\quad d_{n+i}(\pi)=w_i.
\]

It correctly allows leading zeroes, demands a contiguous occurrence, and
treats the empty word as vacuous. It also keeps the incompatible infinite
suffix and subsequence readings separate.

For the frozen adjacent-BBP route, the order of quantifiers is also correct:
one sequence \(N_j\to\infty\) must support the matching and, for each fixed
\(P\geq1\), the lower bound may depend on \(P\). Neither the irrationality
onset nor the sevenfold carry-stability onset is asserted uniformly in
\(P\). This point is essential: the eventual rational coding is a
fixed-\(P\) statement, which is sufficient because finite disagreement for
each fixed \(P\) does not change its lower density along the common
\(N_j\).

## 2. BBP coefficient and modular-row audit

Combining the four fractions in BBP Theorem 1 independently gives

\[
 {4\over8k+1}-{2\over8k+4}-{1\over8k+5}-{1\over8k+6}
 ={120k^2+151k+47\over
   (2k+1)(4k+3)(8k+1)(8k+5)}={c_k\over d_k}.
\]

Every factor of \(d_k\) is odd. The tail majorant used later is global, not a
finite inference: for \(k\geq1\),

\[
 d_k-k^2c_k
 =392k^4+873k^3+665k^2+194k+15>0,
\]

so \(0<a(k)<k^{-2}\). Consequently

\[
 0<\pi-B_n
 <\sum_{k>n}{16^{-k}\over k^2}
 \leq {16^{-n}\over15(n+1)^2}.
\]

Letting \(L_n=\operatorname{lcm}(d_0,\ldots,d_n)\), direct common-denominator
collection gives

\[
 B_n={A_n\over16^nL_n},\qquad
 A_n=\sum_{k=0}^n c_k16^{n-k}{L_n\over d_k}.
\]

With \(\ell_n=L_n/L_{n-1}\), separating the final summand yields exactly

\[
 A_n=16\ell_nA_{n-1}+c_n{L_n\over d_n}.
\]

Multiplication by \(10^n\) cancels to
\(5^nA_n/(8^nL_n)\). Thus for \(q_P=10^P-1\), modulus
\(M_n=8^nL_n\), and least nonnegative residue
\(r_{n,P}\equiv q_P5^nA_n\pmod {M_n}\),

\[
 \|q_Pu_n\|_{\mathbb T}
 ={\min(r_{n,P},M_n-r_{n,P})\over M_n}.
\]

This is an exact integer reformulation only. It supplies no distribution or
noncollapse estimate for the selected residues.

## 3. Uniform energy transfer

Write \(x_n=\{10^n\pi\}\), \(u_n=\{10^nB_n\}\), and let \(E_P,E_P^B\) be
the two squared circle-distance sums in the primary report. Multiplication by
the integer \(q_P\) is \(q_P\)-Lipschitz on the circle. Also

\[
 |\operatorname{dist}(s,0)^2-\operatorname{dist}(t,0)^2|
 \leq \operatorname{dist}(s,t),
\]

because both distances lie in \([0,1/2]\). The BBP tail therefore gives

\[
 |E_P^B(N)-E_P(N)|
 \leq {q_P\over15}\sum_{n\geq0}(5/8)^n
 ={8q_P\over45}.
\]

The endpoint \(n=0\) is covered. The error is uniform in \(N\), so it
preserves both a positive normalized liminf and a logarithmically normalized
liminf.

## 4. Centered carries and the exact density criterion

For fixed \(P\), put \(q=q_P\),

\[
 z_n=\left\lfloor q10^n\pi+\tfrac12\right\rfloor,
 \quad e_n=q10^n\pi-z_n,
 \quad \gamma_n=z_{n+1}-10z_n.
\]

There is no half-integer tie because pi is irrational. Hence
\(e_n\in(-1/2,1/2)\),
\(\gamma_n=10e_n-e_{n+1}\in\{-5,\ldots,5\}\), and iteration gives the
convergent signed expansion

\[
 q\pi=z_0+\sum_{n\geq0}{\gamma_n\over10^{n+1}}.
\]

The forward inequality is exact. For arbitrary real \(a,b\),

\[
 11(10a^2+b^2)-(10a-b)^2=10(a+b)^2\geq0.
\]

Summing this with \(a=e_n,b=e_{n+1}\), and using
\(1_{\gamma_n\ne0}\leq\gamma_n^2\), gives

\[
 K_P(N)\leq121E_P(N)+11(e_N^2-e_0^2)
 \leq121E_P(N)+{11\over4}.
\]

Conversely, if an \(L\)-window beginning at \(n\) contains no nonzero
carry, then \(|e_n|<1/(2\,10^L)\). A nonzero carry belongs to at most \(L\)
of the \(N\) windows under consideration, and all their indices are below
\(N+L\). Therefore

\[
 {E_P(N)\over N}
 \leq {L\over4}{K_P(N+L)\over N}+{1\over4\,10^{2L}}.
\]

For any prescribed \(N_j\to\infty\),
\(|K_P(N_j+L)-K_P(N_j)|\leq L\). The first inequality turns positive carry
density into positive energy; in the other direction, choose fixed \(L\)
large enough that the last term is below half the positive energy liminf.
This proves, without assuming existence of either ordinary limit,

\[
 \liminf_j{E_P(N_j)\over N_j}>0
 \quad\Longleftrightarrow\quad
 \liminf_j{K_P(N_j)\over N_j}>0.
\]

The factor \(121\) is sharp for this generic recurrence: the centered orbit
of \(1/11\) has \(e_n=(-1)^n/11\) and \(\gamma_n=(-1)^n\).

## 5. Sevenfold rational carry coding

At depth \(7n\), direct cancellation gives

\[
 q_P10^nB_{7n}
 ={q_P5^nA_{7n}\over2^{27n}L_{7n}}.
\]

The published source formulation \(\mu(\pi)<8\) has the required
quantifiers: after an onset, every integer numerator and every sufficiently
large positive denominator \(Q\) satisfy
\(|\pi-p/Q|>Q^{-8}\). Taking
\(Q=2q_P10^n\), \(p=2m+1\), and multiplying by \(q_P10^n\) yields uniformly
in the nearest-integer boundary

\[
 \left|q_P10^n\pi-(m+\tfrac12)\right|
 >{1\over2^8q_P^7 10^{7n}}.
\]

Meanwhile the positive BBP tail is at most

\[
 {q_P10^n16^{-7n}\over15(7n+1)^2}.
\]

Their ratio is bounded by

\[
 {2^8q_P^8\over15(7n+1)^2}
 \left({10^8\over16^7}\right)^n\longrightarrow0,
\]

since \(10^8<16^7\). Thus, for each fixed \(P\), the rational shadow and
the true value eventually lie in the same open nearest-integer cell. Their
nearest integers, and hence consecutive carries, agree eventually. This
justifies the rational target in (21h); it does not prove a positive density
of its nonzero terms.

An independent local search also located the existing `machine-checked`
[T35 sevenfold grid-stability module](../../TheoryLib/PiQuantitativeBlockHitting/T35T35OversampledBBPGridStability.lean),
SHA-256
`7374fdaa2aebac7c228408576724c80e5d5558eb515202b45982dfe726f03351`.
It corroborates the exponent-eight numerical comparison for ordinary fixed
decimal block codes. It does not itself specialize to the nearest-integer
carry stream of \(q_P\pi\), so the primary argument above is still needed.

## 6. Irrationality measure gives exactly the logarithmic lower scale

If the nonzero carry positions are \(s_1<s_2<\cdots\), consecutive positions
\(s<s'\) give, with \(a=s+1\),

\[
 |e_a|<\tfrac12 10^{-(s'-a)},\qquad
 \left|\pi-{z_a\over q10^a}\right|<{1\over2q}10^{-s'}.
\]

Zeilberger--Zudilin's published bound
\(7.1032053341370017\ldots<888/125=:M\) permits the eventual lower bound
\(|\pi-p/Q|>Q^{-M}\). With \(Q=q10^a\), comparison gives

\[
 s'<M(s+1)+(M-1)\log_{10}q-\log_{10}2.
\]

Thus \(s_{k+1}\leq Ms_k+C_P\) eventually. Adding
\(C_P/(M-1)\) after enlarging \(C_P\) if necessary converts this to a pure
geometric recurrence. Inverting \(s_k=O_P(M^k)\) yields

\[
 \liminf_{N\to\infty}{K_P(N)\over\log N}
 \geq{1\over\log M}.
\]

The carry-energy inequality and the uniform BBP transfer then give

\[
 \liminf_{N\to\infty}{E_P^B(N)\over\log N}
 \geq{1\over121\log(888/125)}
 =0.004215147560632052\ldots.
\]

The coefficient is independent of fixed \(P\); the onset and additive
constant are not. Dividing by \(N\) still tends to zero, so this bound does
not establish the positive Cesaro liminf required by the parent criterion.

## 7. Kempner--Fredholm separator

For

\[
 \kappa=\sum_{r\geq0}10^{-2^r},
\]

let \(2^r\) be the first power of two above \(n\) and put
\(h=2^r-n\). All earlier decimal spikes become integers after multiplying by
\(10^n\), while the remaining distinct decimal positions give

\[
 \{10^n\kappa\}\leq\sum_{j\geq h}10^{-j}
 ={10^{1-h}\over9}.
\]

For fixed \(q=10^P-1\), therefore,

\[
 \|q10^n\kappa\|_{\mathbb T}^2
 \leq\min\left({1\over4},{q^2 10^{2-2h}\over81}\right).
\]

As \(n\) runs through one gap between powers of two, \(h\) runs through a
finite initial segment of the positive integers. The displayed majorant has
a summable tail and only \(O_P(1)\) saturated terms, so its sum per gap is
\(O_P(1)\). There are \(O(\log N)\) gaps below \(N\).

Kempner's theorem applies to this decimal Fredholm value and supplies
transcendence. Shallit's Theorems 3 and 8--9 apply to
\(B(10,\infty)=\kappa\): its continued-fraction partial denominators belong
to a fixed finite set, so \(\kappa\) is badly approximable and has
irrationality exponent two. For any fixed \(M'>2\), the preceding carry-gap
argument then supplies the matching \(\Omega(\log N)\) lower bound. Hence

\[
 \sum_{n<N}\|q10^n\kappa\|_{\mathbb T}^2
 =\Theta_P(\log N),
 \qquad {1\over N}\sum_{n<N}\|q10^n\kappa\|_{\mathbb T}^2\to0.
\]

Subtracting the first spike \(1/10\) changes the decimal orbit only at the
initial index. The resulting
\(\beta=\sum_{r\geq1}10^{-2^r}\) is exactly the sparse separator in the
independently audited parent report, which has density-one congestion-one
matching with its times-sixteen row. Thus finite irrationality measure plus
that matching cannot imply linear carry density. The separator is not pi and
does not obey the exact BBP four-pole recurrence.

## 8. Source applicability and independent replay

The bounded source check is `literature-checked` on **2026-08-13 UTC**.

| source | independently checked scope |
|---|---|
| Bailey--Borwein--Plouffe, Theorem 1, [DOI](https://doi.org/10.1090/S0025-5718-97-00856-9), local SHA `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` | The source supports the four-pole series, not a periodic-defect density theorem. |
| Zeilberger--Zudilin, [arXiv](https://arxiv.org/abs/1912.06345), printed pp. 407 and 417--418, local SHA `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` | The introduction gives the all-\(p\), sufficiently-large-\(q\), positive-epsilon definition; the final bound is `7.1032053341370017...`. It supplies no digit-density conclusion. |
| Kempner, printed p. 477, [DOI](https://doi.org/10.1090/S0002-9947-1916-1501054-4), local SHA `99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014` | Its transcendence theorem contains the specialization defining \(\kappa\). |
| Shallit, Theorems 3 and 8--9, [PDF](https://cs.uwaterloo.ca/~shallit/Papers/scf.pdf), local SHA `592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981` | For integer \(u\geq3\), and hence \(u=10\), it proves irrationality and bounded continued-fraction partial denominators of \(B(u,\infty)\). |
| Lagarias, Theorems 3.1 and 3.3, [arXiv](https://arxiv.org/abs/math/0101055v2), local SHA `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` | Perturbed-radix shadowing and finite-limit-set rationality do not provide positive frequency. |

A fresh bounded search found the established irrationality-measure result and
generic or metric lacunary literature, but no primary theorem forcing
\(K_P(N)=\Omega(N)\) for fixed pi. This is an applicability record, not an
exhaustive absence or novelty claim.

The disjoint checker is
[bbp_fixed_period_carry_attack_20260813_independent_check.py](bbp_fixed_period_carry_attack_20260813_independent_check.py),
SHA-256
`d784ae344752e5679657a8c61e6aa64f7508d61e72f4bb7a30e59fe44eb15204`.
It imports no primary code and uses different depths, periods, rational seeds,
and construction order. Its retained PASS run contains:

- 401 four-pole/coefficient checks, including the global polynomial tail
  certificate;
- 97 direct common-denominator reconstructions and 485 least-residue checks;
- 4,032 exact metric-grid checks, 16 carry-prefix checks, and 48 window-count
  checks;
- 75 independent sevenfold shadow identities, 72 rational carry checks, and
  exact exponent-eight boundary rescalings;
- the two logarithmic constants to 31 or more decimal places; and
- 128 exact sparse-tail checks and 384 exact finite separator-defect checks.

Run:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_check.py
```

The retained output says `status: PASS` and explicitly sets positive Cesaro
defect, adjacent matching, fixed-sixteen return, and V1 to false. No Lean file
was changed, so this audit adds no theorem to `audit/AxiomAudit.lean` and does
not require the formal verification gate.

## Exact handoff

The fixed-period branch is reduced to the eventually rational statement

\[
 \forall P\geq1:\quad
 \liminf_j{1\over N_j}
 \#\{0\leq n<N_j:\widehat\gamma_{n,P}\ne0\}>0,
\]

on the same sequence used by adjacent matching. Published irrationality
forces only \(\Omega(\log N)\) nonzero carries, and the separator shows this
generic scale is sharp. A further proof must exploit a pi-specific,
cross-index property of the selected four-pole BBP residues to gain the
missing factor \(N/\log N\), or close a different ergodic/matching route.
Neither step is present here. Canonical V1 remains a `conjecture`.
