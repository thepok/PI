# BBP fixed-period carry attack: exact modular defects and the logarithmic barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_adjacent_matching_breakthrough_report.md](bbp_adjacent_matching_breakthrough_report.md),
  SHA-256
  `2b231d3c2e2ef717a2941a0452304ba402915318b72d305f6a6129ee8431f042`;
- [bbp_adjacent_matching_breakthrough_independent_audit.md](bbp_adjacent_matching_breakthrough_independent_audit.md),
  SHA-256
  `32cf25b1b2d00a37de57b325134ba0a53e8f5f6c129b16d3f419000a1620af93`.

## Outcome and claim boundary

No positive Cesaro defect, adjacent-row matching, fixed-sixteen return, or
proof that every finite decimal word occurs in pi was obtained. Canonical V1
remains a `conjecture`.

There is a material exact reduction, recorded as a `proof sketch`.

1. Every periodic-defect term of the rational BBP row has a one-residue
   modular formula with an explicitly updated odd least-common denominator.
2. For \(q_P=10^P-1\), the positive-liminf condition in (40az) is equivalent
   to positive lower density of the nonzero digits in the canonical
   **centered decimal expansion** of \(q_P\pi\), on the same prescribed
   subsequence \(N_j\).
3. Sevenfold oversampling makes that centered digit stream eventually
   **exactly rational**: its nearest integers and carries can be computed from
   the BBP truncations \(B_{7n}\). The published bound \(\mu(\pi)<8\)
   certifies that these shadows cannot cross a nearest-integer boundary.
4. The sharper published bound
   \(\mu(\pi)<888/125=7.104\) forces only logarithmically many nonzero
   centered digits:

   \[
    \liminf_{N\to\infty}{K_P(N)\over\log N}
       \ge {1\over\log(888/125)}.
   \]

   Consequently the unnormalized rational-BBP defect energy satisfies

   \[
    \liminf_{N\to\infty}{1\over\log N}
      \sum_{n=0}^{N-1}\bigl\|(10^P-1)u_n\bigr\|_{\mathbb T}^{2}
    \ge {1\over121\log(888/125)}
    =0.0042151475606\ldots .
   \]

   This is unconditional once the cited published irrationality-measure
   theorem is accepted, but it remains a `proof sketch` here because no new
   Lean declaration or independent audit has checked the assembly.
5. The order cannot be improved from finite irrationality measure alone.
   The transcendental, badly approximable Kempner--Fredholm number has defect
   energy of order \(\log N\) for every fixed \(P\), hence zero normalized
   defect, while also admitting the density-one matching from the frozen
   parent separator.

Thus this branch identifies the missing quantitative jump:

\[
 \boxed{K_P(N)=\Omega(\log N)\quad\hbox{is known, whereas (40az) needs}
        \quad K_P(N_j)=\Omega_P(N_j).}
\]

The finite replay is an `experiment`. The bounded source search is
`literature-checked` on the displayed date. Nothing here is a
`candidate resolution` or a `verified resolution`.

## 1. Normalized target and quantifiers

Canonical V1 is

\[
 \forall m\ge0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists n\ge0\ \forall i<m:\quad d_{n+i}(\pi)=w_i.       \tag{1}
\]

Leading zeroes are allowed, occurrence is contiguous, and the empty word is
vacuous. The two other readings in the canonical source remain separate: an
arbitrary infinite word cannot occur as a suffix, while occurrence as a
subsequence reduces to recurrence of every single digit and is also open.

The frozen adjacent-BBP reduction asks for one sequence \(N_j\to\infty\)
that supports both the matching in (40ak) and, for every fixed \(P\ge1\),

\[
 \liminf_{j\to\infty}{1\over N_j}\sum_{n=1}^{N_j}
 \bigl\|(10^P-1)u_n\bigr\|_{\mathbb T}^{2}>0.             \tag{2}
\]

Here \(P\) is fixed before \(j\to\infty\), the lower bound may depend on
\(P\), and every \(P\) must use the same \(N_j\). Shifting the summation to
\(0\le n<N_j\) changes it by at most \(1/(4N_j)\), so the zero-based
normalization below is equivalent.

## 2. Exact modular form of every rational BBP defect

Write

\[
 a(k)={c_k\over d_k},\qquad
 c_k=120k^2+151k+47,\qquad
 d_k=(2k+1)(4k+3)(8k+1)(8k+5),                       \tag{3}
\]

and

\[
 B_n=\sum_{k=0}^n{a(k)\over16^k},\qquad
 u_n=\{10^nB_n\}.                                    \tag{4}
\]

All \(d_k\) are odd. Put

\[
 L_n=\operatorname{lcm}(d_0,\ldots,d_n),\qquad
 A_n=\sum_{k=0}^n c_k16^{\,n-k}{L_n\over d_k}.        \tag{5}
\]

Then \(A_n\in\mathbb Z\) and

\[
 B_n={A_n\over16^nL_n},\qquad
 u_n=\left\{{5^nA_n\over8^nL_n}\right\}.             \tag{6}
\]

This presentation can be updated without recomputing the sum. If
\(\ell_n=L_n/L_{n-1}\), then

\[
 \boxed{A_n=16\ell_nA_{n-1}+c_n{L_n\over d_n}.}       \tag{7}
\]

For \(q_P=10^P-1\), let

\[
 M_n=8^nL_n,\qquad
 r_{n,P}\equiv q_P5^nA_n\pmod {M_n},\quad
 0\le r_{n,P}<M_n.                                    \tag{8}
\]

The exact periodic defect is

\[
 \boxed{
 \bigl\|q_Pu_n\bigr\|_{\mathbb T}
   ={\min(r_{n,P},M_n-r_{n,P})\over M_n}.}             \tag{9}
\]

Equation (9) is an integer-modular target. It is not a distribution theorem:
the numerator in (8) is the one selected by all preceding four-pole carries,
and no audited result controls its least absolute residue asymptotically.

## 3. The rational row and the true pi row have the same energy scale

Let

\[
 x_n=\{10^n\pi\},\qquad
 E_P(N)=\sum_{n=0}^{N-1}\|q_Px_n\|_{\mathbb T}^2,\qquad
 E_P^B(N)=\sum_{n=0}^{N-1}\|q_Pu_n\|_{\mathbb T}^2. \tag{10}
\]

The audited positive BBP tail gives

\[
 0<10^n(\pi-B_n)\le { (5/8)^n\over15(n+1)^2}.         \tag{11}
\]

Multiplication by \(q_P\) is \(q_P\)-Lipschitz on the circle. Moreover,
\(y\mapsto\operatorname{dist}(y,0)^2\) is one-Lipschitz because the circle
distance takes values in \([0,1/2]\). Hence

\[
 \begin{aligned}
 |E_P^B(N)-E_P(N)|
 &\le q_P\sum_{n=0}^{N-1}10^n(\pi-B_n)\\
 &\le {q_P\over15}\sum_{n\ge0}(5/8)^n
 ={8q_P\over45}.                                    \tag{12}
 \end{aligned}
\]

This uniform \(O_P(1)\) comparison is stronger than the earlier
\(O_P(N^{-1})\) comparison after normalization. In particular it transfers
not only positive Cesaro liminf but also the logarithmic lower bound below.

## 4. Centered carries characterize fixed-period noncollapse

Fix \(P\ge1\), put \(q=q_P\), and define the nearest integers and centered
errors

\[
 z_n=\left\lfloor q10^n\pi+\frac12\right\rfloor,
 \qquad e_n=q10^n\pi-z_n\in(-1/2,1/2).               \tag{13}
\]

There is no half-integer ambiguity because pi is irrational. Define

\[
 \gamma_n=z_{n+1}-10z_n=10e_n-e_{n+1}.              \tag{14}
\]

Then \(\gamma_n\in\{-5,-4,\ldots,5\}\), and iterating
\(e_n=(\gamma_n+e_{n+1})/10\) gives the canonical centered decimal expansion

\[
 \boxed{q\pi=z_0+\sum_{n\ge0}{\gamma_n\over10^{n+1}}.} \tag{15}
\]

Let

\[
 K_P(N)=\#\{0\le n<N:\gamma_n\ne0\}.                 \tag{16}
\]

Two elementary inequalities give an exact density criterion. First,

\[
 (10a-b)^2\le11(10a^2+b^2)                           \tag{17}
\]

because the difference of the right and left sides is \(10(a+b)^2\).
Since a nonzero integer has square at least one, (14) and (17) give

\[
 K_P(N)\le121E_P(N)+{11\over4}.                      \tag{18}
\]

For the reverse direction, fix \(L\ge1\). If none of
\(\gamma_n,\ldots,\gamma_{n+L-1}\) is nonzero, then
\(|e_n|=10^{-L}|e_{n+L}|<1/(2\,10^L)\); otherwise use
\(|e_n|<1/2\). Counting the length-\(L\) windows that meet a nonzero carry
gives

\[
 {E_P(N)\over N}
 \le {L\over4}{K_P(N+L)\over N}+{1\over4\,10^{2L}}. \tag{19}
\]

Equations (18)--(19), followed by first fixing \(L\) and then letting
\(L\to\infty\), prove for every prescribed sequence \(N_j\to\infty\)

\[
 \boxed{
 \liminf_j {E_P(N_j)\over N_j}>0
 \quad\Longleftrightarrow\quad
 \liminf_j {K_P(N_j)\over N_j}>0.}                  \tag{20}
\]

The uniform comparison (12) replaces \(E_P\) by the exact rational modular
energy \(E_P^B\). Thus the whole noncollapse side of the frozen criterion is
equivalent to

\[
 \boxed{
 \forall P\ge1:\quad
 \liminf_j{K_P(N_j)\over N_j}>0}                    \tag{21}
\]

on the same \(N_j\). This is a lower-density theorem about one explicit
signed digit stream for each fixed repunit multiplier \(10^P-1\). It is not
known for pi.

### 4.1 Sevenfold BBP oversampling makes the carries rational

Condition (21) can be made wholly rational. Define

\[
 \widehat z_{n,P}
 =\left\lfloor q_P10^nB_{7n}+\frac12\right\rfloor,
 \qquad
 \widehat\gamma_{n,P}
 =\widehat z_{n+1,P}-10\widehat z_{n,P}.             \tag{21a}
\]

These are exact integer computations. In the notation (5),

\[
 q_P10^nB_{7n}
 ={q_P5^nA_{7n}\over2^{27n}L_{7n}}.                 \tag{21b}
\]

The source-level consequence of \(\mu(\pi)<8\) says that, for all large
denominators \(Q\) and every integer \(p\),

\[
 \left|\pi-{p\over Q}\right|>Q^{-8}.                 \tag{21c}
\]

Apply this with \(Q=2q_P10^n\) and \(p=2m+1\). Uniformly in the
nearest-integer boundary \(m+1/2\),

\[
 \left|q_P10^n\pi-\left(m+\frac12\right)\right|
 >{1\over2^8q_P^7 10^{7n}}.                         \tag{21d}
\]

On the other hand, the BBP tail gives

\[
 0<q_P10^n(\pi-B_{7n})
 \le {q_P10^n16^{-7n}\over15(7n+1)^2}.              \tag{21e}
\]

The ratio of the right side of (21e) to the right side of (21d) is at most

\[
 {2^8q_P^8\over15(7n+1)^2}
 \left({10^8\over16^7}\right)^n\longrightarrow0,    \tag{21f}
\]

because \(10^8<16^7\). Therefore \(q_P10^nB_{7n}\) and
\(q_P10^n\pi\) eventually lie in the same open nearest-integer cell. Hence

\[
 \widehat z_{n,P}=z_n,\qquad
 \widehat\gamma_{n,P}=\gamma_n
 \quad\hbox{for all sufficiently large }n.           \tag{21g}
\]

Finite initial disagreement does not alter lower density. Thus (21) is
equivalently the exact rational-BBP target

\[
 \boxed{
 \forall P\ge1:\quad
 \liminf_j{1\over N_j}
 \#\{0\le n<N_j:\widehat\gamma_{n,P}\ne0\}>0.}       \tag{21h}
\]

This is a computable reformulation, not a proof of its asymptotic lower
bound. It uses the exact oversampling margin \(16^7>10^8\); diagonal depth
\(B_n\) is much too coarse to certify the nearest-integer branch from the
known irrationality exponent.

The coefficient \(121\) in (18) cannot be reduced in the generic centered
recurrence: for \(q\pi\) replaced by \(1/11\), one has
\(e_n=(-1)^n/11\), \(\gamma_n=(-1)^n\), and equality
\(\sum\gamma_n^2=121\sum e_n^2\) at every finite length.

## 5. What the irrationality measure actually supplies

The carries \(\gamma_n\) are nonzero infinitely often. Otherwise (15) would
terminate and make \(q\pi\), hence pi, rational. Enumerate their positions as

\[
 s_1<s_2<s_3<\cdots .                                \tag{22}
\]

For consecutive positions \(s<s'\), all carries from \(s+1\) through
\(s'-1\) vanish. Applying (14) forward from \(a=s+1\) gives

\[
 |e_a|<\frac12\,10^{-(s'-a)}.
\]

Consequently the integer \(z_a\) supplies the rational approximation

\[
 \left|\pi-{z_a\over q10^a}\right|
 <{1\over2q}10^{-s'}.                                \tag{23}
\]

Zeilberger--Zudilin prove
\(\mu(\pi)\le7.103205334137\ldots<888/125\). With

\[
 M={888\over125}=7.104,                              \tag{24}
\]

their definition supplies an onset after which every denominator \(Q\) and
integer numerator \(p\) obey

\[
 \left|\pi-{p\over Q}\right|>Q^{-M}.                 \tag{25}
\]

Use \(Q=q10^a\) in (25) and compare with (23). For all sufficiently large
consecutive carry positions,

\[
 s'<M(s+1)+(M-1)\log_{10}q-\log_{10}2.              \tag{26}
\]

Thus \(s_{k+1}\le Ms_k+O_P(1)\). Adding a fixed constant converts this into
a geometric recurrence, and inversion yields

\[
 \boxed{
 \liminf_{N\to\infty}{K_P(N)\over\log N}
 \ge {1\over\log M}
 ={1\over\log(888/125)}
 =0.5100328548\ldots .}                              \tag{27}
\]

Combining (18), (12), and (27) gives

\[
 \boxed{
 \liminf_{N\to\infty}{E_P^B(N)\over\log N}
 \ge {1\over121\log(888/125)}
 =0.0042151475606\ldots .}                           \tag{28}
\]

The coefficient in (27) is independent of \(P\); only the ineffective onset
and additive constant depend on \(P\). This proves neither (2) nor (21):
after division by \(N\), (28) is only

\[
 {E_P^B(N)\over N}\ge
 \left({1\over121\log(888/125)}-o(1)\right){\log N\over N}. \tag{29}
\]

The lost factor \(N/\log N\) is not a bookkeeping artifact.

## 6. Sharp no-go: finite irrationality measure stops at logarithmic energy

Let

\[
 \kappa=\sum_{r\ge0}10^{-2^r}.                       \tag{30}
\]

Kempner proves this decimal Fredholm value transcendental. Shallit's exact
continued fraction has bounded partial quotients, so \(\kappa\) is badly
approximable and has the optimal irrationality exponent two.

Fix \(P\) and \(q=10^P-1\). If \(2^r\) is the least power of two greater
than \(n\), put \(h=2^r-n\). The decimal tail satisfies

\[
 \{10^n\kappa\}\le {10^{1-h}\over9}.                 \tag{31}
\]

Hence

\[
 \|q10^n\kappa\|_{\mathbb T}^2
 \le\min\left({1\over4},{q^2\,10^{2-2h}\over81}\right). \tag{32}
\]

The sum of the right side over one gap between consecutive powers of two is
bounded by a constant depending only on \(P\). There are \(O(\log N)\) such
gaps below \(N\), so

\[
 \sum_{n<N}\|q10^n\kappa\|_{\mathbb T}^2=O_P(\log N). \tag{33}
\]

Applying the carry-gap proof above with any exponent \(M>2\) gives the
matching lower order \(\Omega(\log N)\). Thus

\[
 \boxed{
 \sum_{n<N}\|q10^n\kappa\|_{\mathbb T}^2
 =\Theta_P(\log N),\qquad
 {1\over N}\sum_{n<N}\|q10^n\kappa\|_{\mathbb T}^2\to0.} \tag{34}
\]

Removing the first decimal spike turns (30) into the exact sparse separator
used in the frozen matching report and changes only finitely many orbit
terms. That report proves density-one, congestion-one indexwise matching
between its decimal row and its times-sixteen row. Therefore all the
following can coexist:

- transcendence;
- irrationality exponent two;
- an infinite topological omega-limit set;
- density-one adjacent matching;
- logarithmically divergent defect energy for every fixed \(P\);
- failure of every normalized fixed-period lower bound in (2).

This separator is not pi and does not satisfy the exact BBP four-pole
coefficient recurrence. Its scope is to rule out any proposed upgrade from
finite irrationality measure, topological excursions, or matching alone to
the positive-density conclusion (21).

## 7. Exact replay and finite diagnostics

The companion
[bbp_fixed_period_carry_attack_20260813_check.py](bbp_fixed_period_carry_attack_20260813_check.py)
has SHA-256
`48a9db36d577376b0229f48c37ae399cdebe62d1a9c0c2959bebd368a4fe9ceb`
and uses integers and `Fraction` for all structural assertions. It

- pins ten input artifacts and primary sources;
- checks (5)--(9) directly against rational partial sums through depth 160;
- evaluates 24,576 exact least-residue defects through depth 2,048 for
  \(P=1,\ldots,12\);
- checks 954 exact forced-carry identities for the rational BBP recurrence;
- computes 3,072 exact sevenfold-oversampled rational carries from
  (21a)--(21b);
- independently replays (15), (18), and (19) on rational centered orbits;
- realizes equality in the constant 121 with the orbit of \(1/11\); and
- runs a separately labeled sparse-Kempner diagnostic through 65,536 terms.

Run:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_check.py
```

The retained run reported `status: PASS`. At depth 2,048 the twelve rational
BBP mean-square defects ranged from \(0.0793260\ldots\) to
\(0.0862125\ldots\), close to the uniform-circle benchmark \(1/12\), while
the smallest individual checked defect was \(1.46\times10^{-6}\). These are
an `experiment`, not evidence for a positive asymptotic liminf. At rational
oversampled carry depth 256, the twelve observed nonzero fractions ranged
from \(0.8789\ldots\) to \(0.9492\ldots\); those finite fractions likewise
prove no lower density. In the Kempner diagnostic the normalized energies
decayed to about \(4\times10^{-6}\) by \(N=65,536\), while energy divided by
\(\log N\) remained bounded at the displayed finite scales. Again, only
(31)--(34), not the finite values, provide the separator proof sketch.

The checker explicitly sets the positive-Cesaro-defect, matching,
fixed-return, and V1 flags to false.

## 8. Literature and mathlib applicability audit

Status of this bounded search: `literature-checked` on **2026-08-13 UTC**.

| source | checked use and boundary | local pin |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | exact four-pole series (3)--(4), not a periodic-defect density theorem | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2), Theorems 3.1 and 3.3 | perturbed-radix shadowing and finite topological limit-set rationality; neither gives positive Cesaro mass | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Zeilberger--Zudilin, [*The Irrationality Measure of Pi is at Most 7.103205334137...*](https://doi.org/10.2140/moscow.2020.9.407), printed pp. 407, 417--418 | source-level exponents used in (21c)--(21f) and (24)--(28); the paper supplies no explicit onset and no digit-density conclusion | `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` |
| Kempner, [*On Transcendental Numbers*](https://doi.org/10.1090/S0002-9947-1916-1501054-4), printed p. 477 | transcendence of (30), used only in the separator | `99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014` |
| Shallit, [*Simple Continued Fractions for Some Irrational Numbers*](https://cs.uwaterloo.ca/~shallit/Papers/scf.pdf), Theorems 3 and 8--9 | bounded partial quotients for the decimal specialization, hence irrationality exponent two | `592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981` |
| local [T36 periodic-window gap](../../TheoryLib/PiPositiveDecimalFactorEntropy/T36T36DecimalPeriodicWindowGap.lean) and [T4 irrationality interface](../../TheoryLib/PiLongLagBlockCollisionDecay/T4T4PublishedIrrationalityOnset.lean) | existing `machine-checked` denominator-window and source-quantifier infrastructure; no new declaration is claimed here | respectively `900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781`, `73a70fc981bc5856e6c52f3c27143d1a54d84373f830c2b1d37faeb2fdbd71de` |

Fresh searches for centered/signed digit density from irrationality measure,
nonzero digits of rational multiples of pi, fixed-irrational lacunary Cesaro
defects, and BBP periodic-defect averages found generic digit-complexity and
metric lacunary results, but no primary theorem giving
\(K_P(N)=\Omega(N)\) for pi. The closest fixed-pi source remains the
ordinary irrationality measure, whose exact consequence is (27), and
Chen--Ye--Zheng's topological progression-slice dispersion, which gives no
frequency. This is an applicability record, not an exhaustive absence or
novelty claim.

A local mathlib search found the usual real floor/round infrastructure and
the repository's existing effective-irrationality interfaces, but no ready
centered-carry density theorem. No formal infrastructure was added. Hence no
new theorem required registration in `audit/AxiomAudit.lean`, and the formal
verification gate was not rerun for this report.

## Sharp handoff

The fixed-period side of the improved adjacent-BBP criterion is now an exact
arithmetic target:

\[
 \forall P\ge1:\quad
 \underline d_{N_j}\{n:\widehat\gamma_{n,P}\ne0\}>0,
 \qquad
 \widehat\gamma_{n,P}\text{ given rationally by (21a)--(21b).} \tag{35}
\]

The diagonal BBP residues (8)--(9) compute the same energy up to the bounded
total error (12), while (21a)--(21h) turn the carry stream itself into an
eventually exact rational BBP stream. Published irrationality gives only the
sharp generic scale \(K_P(N)=\Omega(\log N)\), and the Kempner separator
shows why this cannot be bootstrapped abstractly. A valid next attack must
exploit a genuinely pi-specific cross-index property of the selected
four-pole residues that forces a linear number of centered carries, or bypass
(35) by proving the ergodic/matching alternative through independent
structure. Neither has been proved, so canonical V1 remains a `conjecture`.
