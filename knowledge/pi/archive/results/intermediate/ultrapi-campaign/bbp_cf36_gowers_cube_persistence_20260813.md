# CF36 continuation: Gowers-uniform resonance, selected-unit averaging, and cube persistence

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
'2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825'.
The immutable target is Marcel's local question and has no external source
URL; none is invented here.

Frozen inputs:

| input | SHA-256 |
|---|---|
| [three-primary twisted-sum report](bbp_three_primary_twisted_sum_20260813.md) | '0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12' |
| [three-primary decimation report](bbp_three_primary_decimation_20260813.md) | '29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0' |
| [complement-Fourier report](bbp_complement_fourier_attack_20260813.md) | 'eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a' |
| [high-prime compression report](bbp_high_prime_phase_compression_20260813.md) | '47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564' |

All frozen inputs remained byte-for-byte unchanged in this branch.

## Outcome and claim boundary

Canonical V1 remains a 'conjecture'. No estimate of CF36, no fixed-sixteen
return, and no occurrence theorem for every finite decimal word in pi is
proved here.

The branch does obtain four new conclusions, all with label 'proof sketch'.

1. The isolated three-primary phase is Gowers-uniform at every fixed order:
   its normalized \(U^s\)-norm tends to zero. Nevertheless its complex
   conjugate is a unit-modulus complementary weight with the same small
   \(U^s\)-norm and makes the selected full pairing identically one. In the
   nine-block formula it produces \(D_aW(u)=9\overline{f(u)}\). Thus small
   marginal \(U^2\), \(U^3\), or any fixed \(U^s\) norm of the complement
   cannot by itself imply CF36.
2. Averaging over every unit primary coefficient does give a positive exact
   second-moment theorem. For any unit-modulus complement, only
   \(O_\eta(1)\) unit coefficients can have correlation at least
   \(\eta T\). The actual BBP coefficient, however, is one selected member,
   not an independent sample.
3. The selected endpoint coefficients form one coherent three-adic lift
   tower. The average-case theorem therefore cannot be converted into an
   endpoint theorem by treating successive numerators as fresh samples. An
   artificial maximally resonant complement can obey the same ninth-root
   primary compatibility, so nesting plus marginal Gowers uniformity still
   does not exclude resonance.
4. Expanding second or third van der Corput differences of the nine-block
   inner sum does not terminate the hard phase. Every second-cube term is
   nondegenerate. At a legal dissociated third-lag triple every third-cube
   term is nondegenerate. Each such term retains exponentially deep dyadic
   precision and high-prime logarithmic mass exceeding \(4.54M\) and
   \(4.49M\), respectively, asymptotically. This is a precise persistence
   result, not a lower bound on the exponential sum.

The standalone replay has label 'experiment'. Section 7 is a bounded
'literature-checked' applicability record. This branch adds no formal
declaration and makes no 'machine-checked', 'candidate resolution', or
'verified resolution' claim.

## 1. Normalized target and the CF36 row

Canonical V1 asks that for every \(P\ge1\) and every
\(0\le k<10^P\), some \(n\ge0\) satisfy

\[
             \left\lfloor10^P\{10^n\pi\}\right\rfloor=k,       \tag{GX1}
\]

with leading zeroes retained. It asks for one occurrence of every finite
word, not normality and not an occurrence of every infinite string.

On a last-pre-drop endpoint put

\[
 q=3^e,\qquad T=3^{e-2},\qquad H=T/9=3^{e-4},\qquad
 M={45T-13\over8}.                                      \tag{GX2}
\]

After the frozen exact CRT splits, CF36 is the phase-sensitive pairing of
the isolated primary phase with the actual complement. Harmless constants
removed, the primary factor on the exponent circle is

\[
 f_{e,a}(j)=e_q(a10^j),\qquad j\in\mathbb Z/T\mathbb Z,
 \qquad 3\nmid a.                                      \tag{GX3}
\]

The issue below is not whether \(f_{e,a}\) oscillates: it does so exactly.
The issue is whether the selected BBP complement can track that oscillation.

## 2. Exact fixed-order Gowers decay of the primary phase

For \(s\ge2\), normalize the Gowers norm on \(\mathbb Z/T\mathbb Z\) by

\[
 \|f\|_{U^s}^{2^s}
 =\mathbb E_{x,h_1,\ldots,h_s}
   \prod_{\omega\in\{0,1\}^s}
   \mathcal C^{|\omega|}f(x+\omega\cdot h).       \tag{GX4}
\]

The same three-primary permutation used in the frozen Fourier report gives,
for every integer \(c\),

\[
 \mathbb E_{x\bmod T}e_q(c10^x)
 =e_q(c)\,\mathbb E_{r\bmod T}e_T(cr)
 =\begin{cases}e_q(c),&T\mid c,\\0,&T\nmid c.\end{cases}     \tag{GX5}
\]

Applying (GX5) after \(s\) multiplicative differences shows that a cube can
contribute only if

\[
 T\mid\prod_{i=1}^s(10^{h_i}-1).                  \tag{GX6}
\]

For a nonzero residue \(h\bmod T\), LTE gives

\[
 v_3(10^h-1)=2+v_3(h).                            \tag{GX7}
\]

If \(d=e-2\), the probability of an exact finite valuation \(j<d\) is
\(2/3^{j+1}\); the zero residue has probability \(1/T\). Counting
compositions of the valuations in (GX6) therefore proves, for every fixed
\(s\),

\[
 \boxed{\|f_{e,a}\|_{U^s}^{2^s}
 \le O_s\!\left({e^{s-1}\over T}\right),\qquad
 \|f_{e,a}\|_{U^s}\longrightarrow0.}             \tag{GX8}
\]

For \(s=2\), the frozen sparse Fourier transform makes the answer exact:

\[
                    \boxed{\|f_{e,a}\|_{U^2}^4={9\over T}.}  \tag{GX9}
\]

For \(s=3\), the elementary composition tail gives an explicit version. If
\(e\ge8\), put \(R=e-8\). Then

\[
 \boxed{\|f_{e,a}\|_{U^3}^8
 \le {3\over T}+{2(R+2)^2\over3^{R+1}}
 ={3+486(e-6)^2\over T}.}                         \tag{GX10}
\]

The right side is intentionally only an upper bound: phases among the
supported cubes can cancel further. Equations (GX8)--(GX10) are already
enough for the following sharp information-scope no-go.

## 3. A Gowers-uniform complement can resonate maximally

Take the artificial unit-modulus complement

\[
                         W_{e,a}(j)=\overline{f_{e,a}(j)}.     \tag{GX11}
\]

It has exactly the same \(U^s\)-norm as \(f_{e,a}\), so (GX8) says that it
is Gowers-uniform at every fixed order. Yet

\[
                  {1\over T}\sum_{j<T}f_{e,a}(j)W_{e,a}(j)=1. \tag{GX12}
\]

This is not merely a Fourier-coordinate construction. The exact
nine-block law

\[
 f_{e,a}(u+mH)=f_{e,a}(u)e_9(am)                  \tag{GX13}
\]

gives, with the frozen block operator,

\[
 \boxed{D_aW_{e,a}(u)
 =\sum_{m=0}^8e_9(am)W_{e,a}(u+mH)
 =9\overline{f_{e,a}(u)}.}                        \tag{GX14}
\]

Thus the CF36 inner product is \(9H=T\), even though both marginal factors
have vanishing fixed-order Gowers norms. A generalized von Neumann argument
would need a norm that controls correlation **relative to this specific
primary test**; a marginal \(U^s(W)\) estimate is logically insufficient.

The weight (GX11) is not asserted to be the BBP complement. Its role is to
falsify any deduction that uses only unit modulus, small fixed-order Gowers
norms, and the nine-block geometry while discarding the selected relative
phase.

## 4. Positive unit-coefficient orthogonality, and its exact limit

There is a genuine average-case theorem. For any unit-modulus
\(W:\mathbb Z/T\mathbb Z\to\mathbb C\), define

\[
 S_a(W)=\sum_{j\bmod T}e_q(a10^j)W(j),\qquad
 a\in(\mathbb Z/q\mathbb Z)^\times.                        \tag{GX15}
\]

Ramanujan orthogonality modulo \(3^e\) is nonzero off the diagonal only when
\(j-k\equiv T/3\) or \(2T/3\pmod T\). In those two cases its normalized
value is \(-1/2\). Hence the exact second moment is

\[
 \boxed{{1\over\varphi(q)}\sum_{3\nmid a}|S_a(W)|^2
 =T-\Re\sum_{j\bmod T}W(j+T/3)\overline{W(j)}\le2T.}          \tag{GX16}
\]

Since \(\varphi(q)=6T\), Markov's inequality gives the depth-independent
exceptional count

\[
 \boxed{\#\{a:3\nmid a,\ |S_a(W)|\ge\eta T\}
 \le {12\over\eta^2}.}                              \tag{GX17}
\]

Thus, for each fixed complement row, all but \(O_\eta(1)\) primary
coefficients have no macroscopic correlation. This is a real narrowing of
CF36: one need not control a positive proportion of coefficients, but one
must still exclude the single selected BBP coefficient.

The resonant example shows sharpness at exactly that logical boundary. For
\(W=\overline{f_{e,a_0}}\), one has \(S_{a_0}(W)=T\), while

\[
 \sum_jW(j+T/3)\overline{W(j)}=T e_3(-a_0),
\]

so the unit-average second moment is \(3T/2\). A single exceptional unit is
fully compatible with (GX16)--(GX17).

## 5. The selected coefficients are a coherent lift, not fresh samples

Let

\[
 U_e=3^eB_{M_e^-}\in\mathbb Z_{(3)}^\times,\qquad
 a_e\equiv hU_e10^{M_e^-}\pmod {3^e},             \tag{GX18}
\]

for fixed \(3\nmid h\). The frozen decimation report proves
\(U_e\equiv U_{e-2}\pmod {3^{e-2}}\). Also

\[
 M_e^--M_{e-2}^-=5\,3^{e-2},\qquad
 \operatorname {ord}_{3^{e-2}}(10)=3^{e-4}.       \tag{GX19}
\]

Therefore

\[
                  \boxed{a_e\equiv a_{e-2}\pmod {3^{e-2}}.} \tag{GX20}
\]

The selected coefficients follow one three-adic path through the nine lifts
at each new endpoint. Equations (GX16)--(GX17) do not say that this path
avoids the \(O_\eta(1)\) exceptional coefficients.

Even the artificial resonance can respect the primary nesting. On the
first \(T_{e-2}=T_e/9\) exponents, (GX20) gives

\[
                    \boxed{W_{e,a_e}(u)^9=W_{e-2,a_{e-2}}(u).} \tag{GX21}
\]

Equation (GX21) is not the four-pole BBP complement recurrence. It proves
the bounded no-go that three-adic coefficient nesting, ninth-root primary
compatibility, and marginal fixed-order uniformity still admit maximal
relative resonance. A successful cross-depth argument must use additional
actual-complement information.

## 6. Second and third cube persistence in the actual complement factors

The preceding no-go is abstract. A separate exact calculation shows why a
second or third van der Corput step does not make the actual growing factors
terminal. Let \(0<d_i<H\), choose a block index
\(m_\omega\in\{0,\ldots,8\}\) at every cube vertex, and put

\[
 C_{\mathbf m,\mathbf d}
 =\sum_{\omega\in\{0,1\}^s}(-1)^{|\omega|}
   10^{m_\omega H+\omega\cdot\mathbf d}.          \tag{GX22}
\]

After expanding an \(s\)-fold multiplicative difference of the CF36 inner
block, every dyadic and high-prime factor has exponent coefficient

\[
 {10^{M+u}\over16}C_{\mathbf m,\mathbf d};        \tag{GX23}
\]

the constant \(-1\) in \(A_n=10^n/16-1\) cancels. Also

\[
 |C_{\mathbf m,\mathbf d}|
 \le2^s10^{8H+d_1+\cdots+d_s}
 <2^s10^{(8+s)H}.                                 \tag{GX24}
\]

For \(s=2\), \(C_{\mathbf m,\mathbf d}\ne0\) for **every** positive lag
pair and every choice of four block indices. Indeed, equality of two sums
of two powers of ten forces equality of their exponent multisets: all
decimal digits are at most two, so there is no carry. But an even-parity
cube exponent cannot equal an odd-parity exponent, since their difference
would make either \(d_1\) or \(d_2\) a nonzero multiple of \(H\).

For \(s=3\), zero is possible only through literal equality of the two
four-element exponent multisets; again every digit is at most four, so no
carry is possible. In particular, if the eight subset sums of
\(d_1,d_2,d_3\) are distinct modulo \(H\), no third-cube coefficient
vanishes. The legal choice

\[
                         (d_1,d_2,d_3)=(1,2,4),\qquad H>7,    \tag{GX25}
\]

has this property.

Now use the frozen squarefree high-prime product, whose logarithmic mass is
\((5+o(1))M\). For fixed \(h\ne0\) and large \(M>|h|\), a selected prime
is annihilated in a nondegenerate cube term only if it divides
\(C_{\mathbf m,\mathbf d}\). The product of all annihilated selected primes
therefore divides \(|C_{\mathbf m,\mathbf d}|\). Since
\(H=(8M+13)/405\), (GX24) gives the surviving mass

\[
 \boxed{\log Q_{M,s}^{\rm surv}\ge
 \left(5-{8(8+s)\log10\over405}+o(1)\right)M.}    \tag{GX26}
\]

For second and third differences the respective constants are

\[
                   4.545168376692534\ldots,\qquad
                   4.499685214361788\ldots.       \tag{GX27}
\]

The dyadic factor persists as well. With
\(K_M=4M-v_2(M+1)\), cancellation in (GX23) leaves exponent at least

\[
 K_M-M-u-v_2(h)-v_2(C_{\mathbf m,\mathbf d}).     \tag{GX28}
\]

For nonzero \(C\), the elementary bound
\(v_2(C)\le\log_2|C|\), followed by (GX24), yields

\[
 \boxed{L_{M,s}\ge
 \left(3-{8(1+(8+s)\log_2 10)\over405}+o(1)\right)M.}       \tag{GX29}
\]

The constants for \(s=2,3\) are

\[
                   2.324063586195089\ldots,\qquad
                   2.258445253456573\ldots.       \tag{GX30}
\]

Thus every second-cube term, and every third-cube term at the dissociated
lags (GX25), still contains a dyadic character with exponentially deep
precision and a primitive high-prime character of exponential modulus,
while the summation length is only \(H=\Theta(M)\). Second and third
differencing do not produce a polynomial-style constant or a bounded-factor
complete sum.

Equations (GX26)--(GX30) do **not** show that those correlations are large.
Simultaneous phase cancellation among the retained factors could still
prove CF36. Their exact scope is narrower: another fixed number of formal
differences, or a theorem applied to one marginal factor, does not remove
the already isolated hard family.

## 7. Mathlib and primary-literature applicability

### literature-checked

Search and direct-check date: **2026-08-13 UTC**.

- The local mathlib and verified-track search found the deterministic
  van der Corput core in T66 but no existing definition or theorem for
  Gowers norms. No new formal infrastructure was introduced for this
  'proof sketch'.
- W. T. Gowers,
  [*A New Proof of Szemerédi's Theorem*](https://doi.org/10.1007/s00039-001-0332-9),
  develops higher-degree uniformity in its intended multilinear setting.
  It does not state that small \(U^s\) norms for two separately chosen
  functions force their pointwise inner product to be small; (GX11)--(GX14)
  give an exact counterexample to that transfer here.
- B. Green and T. Tao,
  [*Linear Equations in Primes*](https://doi.org/10.4007/annals.2010.171.1753),
  Appendices B--C develop Gowers box norms and generalized von Neumann
  estimates for systems of linear forms. CF36 instead pairs a selected
  three-adic exponential with a complement built from the same BBP
  numerator and changing CRT modulus. The hypotheses do not turn the
  marginal bound in (GX8) into control of that selected conjugate pairing.
- The fixed-order geometric-difference identity and the available Korobov
  sum ranges were already checked in the frozen complement-Fourier and
  weighted-differencing reports. No primary source found there estimates
  the nondegenerate mixed cube family (GX22)--(GX23) at logarithmic length.

This is a bounded applicability statement, not an exhaustive search or a
novelty claim. No external theorem is used to prove (GX5)--(GX30); those
are elementary finite-group, valuation, and integer-size calculations.

## 8. Standalone exact replay

The [checker](bbp_cf36_gowers_cube_persistence_20260813_check.py), SHA-256
'24adf41ff8197d354ea8a5569dbb227f521346e96287006d013b77e6fb3fdea9',
imports no other branch checker. It verifies the frozen hashes, exact
sparse-support and nine-block congruences, the valuation-count support bound
behind (GX10), the Ramanujan support in (GX16), the resonant \(T/3\)
correlation, all displayed endpoint coefficient lifts, every one of 419,904
second-cube coefficients on the first \(H=9\) row, 6,561 third-cube samples
at the dissociated lags, and the constants in (GX27) and (GX30).

Run from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_check.py

The retained run reported:

    asserts_cf36_bound=False
    asserts_fixed_return=False
    asserts_v1=False
    dyadic_constant_k2=2.324063586195088918939196162076169841804477749526
    dyadic_constant_k3=2.2584452534565731194750910869257621346269008331206
    endpoint_nesting_checks=20
    high_constant_k2=4.5451683766925341858729893422845700330664490886659
    high_constant_k3=4.4996852143617876044602882765130270363730939975325
    nine_block_checks=45
    ramanujan_pattern_checks=66429
    resonance_checks=66429
    second_cube_checks=419904
    size_bound_checks=419904
    sparse_support_checks=66429
    third_cube_checks=6561
    u3_support_checks=5
    valuation_bound_checks=419904
    exact_record_sha256=12253c483c206d11e741f6656b1f3dad61042ac0bef312fd697c28d04ce4d2fb
    status=PASS

Every bounded enumeration has label 'experiment'. It checks the algebra
and catches boundary mistakes; it is not the all-depth proof of the displayed
'proof sketch' statements.

## 9. Coordination record and sharp handoff

This branch registered descendant-area watch
'ultrapi-cf36-gowers-20260813' on 'local:pi-digits' for agent
'codex-ultrapi-cf36-gowers'. Its initial poll was empty at cursor and
delivered sequence 57,404, so no event was acknowledged. Observation events
are coordination signals only and were not used as mathematical evidence.

The new positive statement is (GX16)--(GX17): at every endpoint only
finitely many, uniformly bounded in depth, unit primary coefficients can
remain macroscopically correlated with the complement. The new obstruction
is that the BBP coefficient follows one coherent lift path and could be one
of those exceptions; marginal Gowers decay cannot exclude it, even together
with ninth-root compatibility. Meanwhile (GX26)--(GX30) show that a second
or third differencing pass leaves the actual hard moduli intact term by term.

The viable continuation is therefore sharply selected: prove that the
actual complement makes the coherent coefficient \(a_e\) avoid the
\(O_\eta(1)\) exceptional set along an unbounded endpoint sequence, or bound
the relative correlation directly. No such estimate is obtained here, so
canonical V1 remains a 'conjecture'.
