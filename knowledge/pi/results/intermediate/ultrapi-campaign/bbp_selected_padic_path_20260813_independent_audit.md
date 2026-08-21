# Independent audit of the selected coherent three-adic BBP path

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Audited artifacts:

| artifact | SHA-256 |
|---|---|
| [primary report](bbp_selected_padic_path_20260813.md) | `5d8a4259ec2ad4f0f0f0d77558ce854ac345a79b10b672060419cc6445e67481` |
| [primary checker](bbp_selected_padic_path_20260813_check.py) | `24f8858a1c80a4df6710c21d5aa09d8d7d4e2a402f789c0c41c9e6b95ff74563` |

## Verdict and claim boundary

**PASS with one scope clarification.**  The all-even-epoch defect congruence,
the carry-sensitive lift formula, the exact rows through (e=14), and the
(a_{16}) prediction all survive an independent derivation and a disjoint
standard-library replay.  No fatal mathematical or reproducibility issue was
found.

The clarification concerns the phrase “the visible coefficient is not a
Markov state.”  The collision (a_4=a_6=a_8=29) rules out an
epoch-independent transition law whose entire input is the **bare canonical
integer** (a_e).  If the modulus (3^e), the epoch (e), or hidden digits
are included in the state, the three inputs are no longer the same state.
The primary report already distinguishes this narrow claim from an
all-encodings claim, so this is a scope clarification rather than a defect.

The all-depth deductions retain label `proof sketch`.  The bounded rational
and modular replay retains label `experiment`.  The dated source and
applicability check retains label `literature-checked`.  Canonical V1 remains
a `conjecture`; there is no selected-correlation decay theorem, deterministic
exceptional-fibre escape, `candidate resolution`, or `verified resolution`.
This audit adds no formal declaration and makes no `machine-checked` claim.

## 1. Normalized target and quantifiers

Canonical V1 is

\[
 \forall P\ge1\ \forall k\in\{0,\ldots,10^P-1\}\ \exists n\ge0:
 \qquad \left\lfloor10^P\{10^n\pi\}\right\rfloor=k,               \tag{IA1}
\]

where (k) is padded to exactly (P) decimal digits.  It asks for one
contiguous occurrence of each finite word.  It does not ask for normality,
positive frequency, infinite recurrence, or the occurrence of an arbitrary
infinite string.

The audited branch instead studies one coherent three-adic coefficient path.
For even (e\ge2), put

\[
 M_e={5\cdot3^e-13\over8},\qquad
 B_e=\sum_{k=0}^{M_e}\sum_{i=1}^4 f_i(k),\qquad
 U_e=3^eB_e,                                                   \tag{IA2}
\]

with

\[
 f_i(k)={c_i\over(a_i k+b_i)16^k},\quad
 (a_i,b_i,c_i)=(8,1,4),(2,1,-1/2),(8,5,-1),(4,3,-1/2).         \tag{IA3}
\]

The selected representative is

\[
 a_e\equiv U_e10^{M_e}\pmod {3^e},\qquad0\le a_e<3^e.          \tag{IA4}
\]

The question “is this path finite-state?” is ambiguous unless one specifies
whether the epoch, modulus, hidden digits, or a pole-shell summary belongs to
the state.  The audited collision answers only the narrow bare-(a_e)
version.

## 2. Exact decimation and every cutoff

For the four poles define

\[
                 m=(1,4,1,2),\qquad d=(1,4,5,6).                \tag{IA5}
\]

These constants are not fitted from data: (m_i=8/a_i) and
(d_i=m_ib_i).  Hence, writing (A_i(r)=a_ir+b_i),

\[
 a_i(9r+d_i)+b_i=9A_i(r),\qquad
 9r+d_i-r=m_iA_i(r).                                           \tag{IA6}
\]

It follows identically that

\[
 9f_i(9r+d_i)-f_i(r)
   =f_i(r)\bigl(16^{-m_iA_i(r)}-1\bigr).                        \tag{IA7}
\]

Let (M=M_e) and (N=M_{e+2}).  Direct substitution gives

\[
                    N=9M+13,qquad M\equiv N\equiv4\pmod9.      \tag{IA8}
\]

The inclusive paired cutoffs are therefore

\[
 Q_i=\left\lfloor{N-d_i\over9}\right\rfloor
              =(M+1,M+1,M,M).                                 \tag{IA9}
\]

Subtracting the old partial sum from the decimated new one gives, with no
missing endpoint,

\[
\begin{aligned}
 D_e:=9B_{e+2}-B_e={}&f_1(M+1)+f_2(M+1)\\
 &+\sum_i\sum_{r=0}^{Q_i}\bigl(9f_i(9r+d_i)-f_i(r)\bigr)\\
 &+\sum_i\sum_{\substack{0\le k\le N\\k\not\equiv d_i\ (9)}}9f_i(k).
                                                                    \tag{IA10}
\end{aligned}
\]

For (i=1,2), adding (f_i(M+1)) compensates for the extra
(-f_i(M+1)) introduced by extending the paired difference to (Q_i=M+1).
For (i=3,4), (Q_i=M), so there is no boundary term.  This verifies both
the signs and the four inclusive pair counts.

## 3. Paired terms in (3\mathbb Z_{(3)})

Fix a pole, set (A=ar+b=3^ju) with (3\nmid u), and put (t=mA).
The paired error (E=f(r)(16^{-t}-1)) satisfies

\[
 {E\over3}
 =-5cm\,16^{-(r+t)}Q_t,qquad
 Q_t={16^t-1\over15t}.                                         \tag{IA11}
\]

The step (Q_t\equiv1\pmod{3\mathbb Z_{(3)}}), including when
(3\mid t), deserves an explicit valuation check.  The binomial expansion
gives

\[
 Q_t=1+\sum_{s=2}^t {\binom ts\over t}15^{s-1}.                 \tag{IA12}
\]

Since

\[
 v_3\!\left({\binom ts\over t}15^{s-1}\right)
 \ge s-1-v_3(s)\ge1\qquad(s\ge2),                              \tag{IA13}
\]

every nonconstant term vanishes modulo three.  Also
(-5\equiv1\pmod3) and every power of (16) is (1pmod3).  Thus

\[
                  E\in3\mathbb Z_{(3)},\qquad E/3\equiv cm\pmod3. \tag{IA14}
\]

The inclusive pair counts are (Q_i+1).  Because (M\equiv4\pmod9),

\[
             (Q_i+1)_{i=1}^4\equiv(0,0,2,2)\pmod3.             \tag{IA15}
\]

This gives paired contributions (0,0,3,3pmod9), respectively.

## 4. Nonlift residues and boundaries

For a nonpaired index, (v_3(a_ik+b_i)\le1).  A height-zero term is zero
after multiplication by nine modulo nine.  If (a_ik+b_i=3u), then

\[
                    9f_i(k)\equiv3c_i u^{-1}\pmod9.             \tag{IA16}
\]

In each complete block modulo nine, the two height-one residues have
(u\equiv1,2\pmod3); their contributions cancel.  Since (N\equiv4pmod9),
only the final residues (k=0,1,2,3,4) survive.  Enumerating them gives
the partial contributions (6,3,6,0pmod9).  The two regular boundaries
occur at (M+1\equiv5\pmod9), giving (2,5,0,0pmod9).

The entire independently derived table is

| pole | inclusive pair count mod (3) | paired | partial nonlift | boundary | total mod (9) |
|---:|---:|---:|---:|---:|---:|
| 1 | 0 | 0 | 6 | 2 | 8 |
| 2 | 0 | 0 | 3 | 5 | 8 |
| 3 | 2 | 3 | 6 | 0 | 0 |
| 4 | 2 | 3 | 0 | 0 | 3 |

Therefore

\[
                         \boxed{D_e\equiv1\pmod {9\mathbb Z_{(3)}}} \tag{IA17}
\]

for every even (e\ge2).  There is no exceptional small cutoff: for
(e=2), (M=4), (N=49), and (Q=(5,5,4,4)), so the same inclusive
counts and final residue block apply literally.  A separate exact `Fraction`
sum also gives (D_2,D_4,D_6\equiv1\pmod9).

Because

\[
 U_{e+2}-U_e=3^e(9B_{e+2}-B_e)=3^eD_e,                         \tag{IA18}
\]

(IA17) is equivalently the shell law

\[
                     U_{e+2}-U_e\equiv3^e\pmod {3^{e+2}}.       \tag{IA19}
\]

Here every congruence is in the localization (mathbb Z_{(3)}):
(x\equiv y\pmod{3^s\mathbb Z_{(3)}}) means
(x-y\in3^s\mathbb Z_{(3)}).  Equation (IA10) explicitly shows that
(D_e\in\mathbb Z_{(3)}), so no illegal reduction of a denominator divisible
by three is being made.

## 5. The hidden carry and exact lift

Let (x_e) be the canonical representative of
(U_e10^{M_e}pmod {3^{e+2}}), and write

\[
              x_e=a_e+\ell_e3^e,qquad0\le\ell_e<9.             \tag{IA20}
\]

The depth increment is (M_{e+2}-M_e=5\cdot3^e).  LTE gives the exact
valuation

\[
 v_3\!\left(10^{5\cdot3^e}-1\right)
 =v_3(10-1)+v_3(5\cdot3^e)=e+2,                                \tag{IA21}
\]

so (10^{M_{e+2}}\equiv10^{M_e}\pmod {3^{e+2}}).  Combining this with
(IA19), and using (10^{M_e}\equiv1\pmod9), yields

\[
\begin{aligned}
 a_{e+2}
 &\equiv U_{e+2}10^{M_{e+2}}\\
 &\equiv x_e+3^eD_e10^{M_e}\\
 &\equiv a_e+3^e(\ell_e+1)\pmod {3^{e+2}}.                     \tag{IA22}
\end{aligned}
\]

Writing the unique canonical lift as
(a_{e+2}=a_e+\kappa_e3^e), (0\le\kappa_e<9), proves

\[
                         \boxed{\kappa_e\equiv\ell_e+1\pmod9}. \tag{IA23}
\]

Thus (D_e\equiv1) supplies only the universal **defect** digit.  It does
not make every selected lift equal to one, because (a_e\bmod3^e) omits
the two digits (ell_e).

## 6. Disjoint exact replay through (e=14)

### `experiment`

The new
[independent checker](bbp_selected_padic_path_20260813_independent_check.py),
SHA-256
`0cb582ab0a523d412d831a3fe76f9bcb3ee6ffab8f880d6a343e12b87a786ef3`,
imports no primary checker and uses only the Python standard library.  Unlike
the primary combined-rational summand, it sums the four poles separately.
It makes one scan with common scale (3^{14}) and precision (3^{16});
exact divisibility by (3^{14-e}) then recovers (U_e\pmod {3^{e+2}}) at
each earlier endpoint.  It also independently:

- enumerates every paired and nonlift residue entering (IA17);
- checks the endpoint algebra at 80 even epochs;
- evaluates literal four-pole `Fraction` sums for (D_2,D_4,D_6);
- checks the shell law between every adjacent computed pair;
- exhausts the usual affine order-one and order-two laws modulo nine.

The reproduced rows are:

| (e) | (M_e) | (U_e\bmod3^e) | (a_e) | (ell_e) | (kappa_e) |
|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 2 | 2 | 2 | 3 |
| 4 | 49 | 38 | 29 | 8 | 0 |
| 6 | 454 | 524 | 29 | 8 | 0 |
| 8 | 4,099 | 4,898 | 29 | 3 | 4 |
| 10 | 36,904 | 57,386 | 26,273 | 2 | 3 |
| 12 | 332,149 | 175,484 | 203,420 | 2 | 3 |
| 14 | 2,989,354 | 3,364,130 | 1,797,743 | 0 | 1 |

The (e=14) row is a fresh exact modular sum of all four poles, not a
floating-point or FFT replay.  Since (ell_{14}=0), (IA23) gives

\[
            \boxed{a_{16}=a_{14}+3^{14}=1,797,743+4,782,969=6,580,712}. \tag{IA24}
\]

The lift word is (3,0,0,4,3,3,1).  Under the conventional definitions

\[
 x_{n+1}=\alpha x_n+\beta,qquad
 x_{n+2}=\alpha x_{n+1}+\beta x_n+\gamma\pmod9,                 \tag{IA25}
\]

exhaustion finds zero fitting affine laws of either order.  This finite fact
does not imply nonautomaticity or exclude a different finite augmentation.

The retained
[record](bbp_selected_padic_path_20260813_independent_record.txt), SHA-256
`c3e3b8798cd699a0c9ac65c2670796d43b0b21bdbc05f381043094c0dbb3406c`,
reports `status=PASS` and exact-record SHA-256
`ab6b5f4a7d4d8ffd38e59377c120b17581b2592f1530eaad7f593a287cfeae4b`.
The retained run used 37.36 seconds and 17,920 KiB maximum resident memory.

The primary checker was separately compiled and rerun.  It reported
`status=PASS`, reproduced exact-record SHA-256
`fb3e99511c46f3cbe2d6772dcbae5fc7e33516cde7ef9c1a1ccf2c4035e1d9a0`,
and used 25.32 seconds and 17,792 KiB maximum resident memory.

## 7. What the repeated state does and does not show

The three equal bare values

\[
                         a_4=a_6=a_8=29                           \tag{IA26}
\]

have next lifts (0,0,4).  Therefore no single-valued function
(F:\mathbb Z_{\ge0}\to\mathbb Z/9\mathbb Z) with
(kappa_e=F(a_e)) can govern all three transitions.  This is the exact
narrow no-go claimed by the primary report.

It does not rule out (F(e,a_e)), a state that remembers the modulus, a
state containing (ell_e), a finite pole-shell summary, or an unbounded
precision state.  In particular, the residues “29 modulo (3^4),” “29
modulo (3^6),” and “29 modulo (3^8)” are distinct typed objects if the
ambient rings are retained.  Calling them the same state is justified only
after explicitly projecting to the bare integer, as the primary report does.

## 8. Mathlib and primary-literature applicability

### `literature-checked`

Direct-check date: **2026-08-13 UTC**.

- Bailey--Borwein--Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic Constants*](https://www.ams.org/mcom/1997-66-218/S0025-5718-97-00856-9/S0025-5718-97-00856-9.pdf),
  supplies the four-pole series and digit-extraction setting.  It does not
  state selected three-adic carry decay or decimal word coverage.
- Delaygue--Rivoal--Roques,
  [*On Dwork's p-adic Formal Congruences Theorem and Hypergeometric Mirror
  Maps*](https://arxiv.org/abs/1309.5902), concerns specified generalized
  hypergeometric series with rational parameters.  No transformation of the
  moving BBP endpoint sum into its hypotheses is provided.
- Abram--Lagarias,
  [*p-adic path set fractals and arithmetic*](https://arxiv.org/abs/1210.2478),
  starts from digit paths presented by a finite automaton and proves closure
  properties.  It does not infer an automaton for this BBP path.
- Christol--Kamae--Mendès France--Rauzy,
  [*Suites algébriques, automates et substitutions*](https://www.numdam.org/articles/10.24033/bsmf.1926/),
  characterizes coefficient sequences of algebraic formal power series over
  finite fields.  No algebraic formal-series equation or finite kernel for
  the characteristic-zero moving truncations in (IA2) is known here.

A fresh local search found mathlib's standard `padicValRat`, rational
congruence, and finite-sum infrastructure, including extensive local uses in
the quantitative-block-hitting track.  It found no automatic-sequence library
or declaration recognizing the BBP carry path.  These sources support the
primary applicability boundary; none supplies the missing selected-path
theorem.  This is a bounded applicability check, not an exhaustive novelty
survey.

## 9. Hygiene, coordination, and handoff

All relative links in the primary report resolve.  The canonical source,
primary report, primary checker, independent checker, retained record, and
this audit are free of forbidden C0 control bytes.  The claim vocabulary is
used with the scopes stated above.  Neither checker imports the other, and
the frozen source/report/checker hashes are enforced at runtime.

This audit registered descendant-area watch
`ultrapi-padic-path-audit-20260813` on `local:pi-digits` for agent
`codex-ultrapi-audit-selected-padic`.  Its initial poll was empty at cursor
and delivered sequence 57,501.  Its final pre-verdict poll was also empty at
the same cursor and delivered sequence, so no event was acknowledged.
Observation events are coordination signals only and supplied no mathematical
evidence.

The durable advance is the exact all-depth defect digit and the identification
of the missing state variable.  The obstruction is equally exact: each new
selected lift requires two digits of (U_e10^{M_e}) beyond the visible
modulus.  No all-depth recurrence, complexity lower bound, or selected
correlation estimate controls those digits.  Consequently this branch does
not approach canonical V1 unless a genuinely new theorem governs the hidden
carry sequence or bypasses it with a direct selected-correlation estimate.
