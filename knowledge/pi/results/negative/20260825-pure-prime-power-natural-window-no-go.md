# Pure prime-power structure does not force natural-window cancellation

Status: `proof sketch`

Source: `workflows/state/chatgpt-pro/20260825-open-frontier-creative-be/turns/0004/answer.md`

## Scoped obstruction

Pure prime-power denominators, unit numerators, maximal prime-power
conductors for every finite terminal-unit time stencil, and exact Parseval
orthogonality over the complete modulus do **not** imply cancellation in the
much shorter natural Fourier window.

The separator is elementary.  Put

\[
\alpha=\frac19,
\qquad
U_m=
\begin{cases}
\lfloor 13^m\alpha\rfloor,&13\nmid\lfloor 13^m\alpha\rfloor,\\
\lfloor 13^m\alpha\rfloor+1,&13\mid\lfloor 13^m\alpha\rfloor,
\end{cases}
\qquad
R_m=\frac{U_m}{13^m}.
\]

Then `13 ∤ U_m`, the displayed fraction is reduced, and

\[
|\alpha-R_m|\le 13^{-m}.
\]

For `k >= 1`, define the decimal-scaled carrier

\[
X_{k,n}=10^nR_{k+n}=\frac{10^nU_{k+n}}{13^{k+n}}.
\]

If `c_0,...,c_R` are integers with `13 ∤ c_R`, reduction over the
common denominator gives the exact terminal-unit law

\[
v_{13}\!\left(\sum_{r=0}^R c_rX_{k,n+r}\right)=-(k+n+R).
\]

Indeed, modulo `13` only the terminal numerator
`c_R 10^(n+R) U_(k+n+R)` survives.  Thus every such finite stencil has the
maximal possible 13-primary denominator.

There is also exact complete-modulus orthogonality.  For `N >= 1`, let
`P=13^(k+N-1)`.  Writing

\[
X_{k,n}=\frac{A_n}{P},
\qquad
A_n=10^nU_{k+n}13^{N-1-n},
\]

the distinct valuations `v_13(A_n)=N-1-n` make the `A_n` pairwise distinct
modulo `P`.  Hence, for arbitrary complex `b_n`, additive-character
orthogonality gives

\[
\sum_{h=0}^{P-1}
  \left|\sum_{n=0}^{N-1}b_ne(hX_{k,n})\right|^2
=P\sum_{n=0}^{N-1}|b_n|^2.
\]

Nevertheless the low frequency `h=9` is maximally coherent.  Since
`10^n/9` has fractional part `1/9`,

\[
e(9\cdot10^n\alpha)=1
\]

for every `n`, while the phase Lipschitz bound and the geometric error give

\[
\left|\sum_{n=0}^{N-1}e(9X_{k,n})-N\right|
\le 78\pi\,13^{-k}.
\]

Thus the complete-modulus Parseval identity can coexist with essentially
trivial cancellation at a fixed frequency lying inside every relevant
natural window.  The modulus `P=13^(k+N-1)` is simply far larger than the
window `|h|<2\cdot10^k`; its total energy estimate does not control how energy
is distributed in that initial window.

## Claim boundary

This is a generic quantization counterexample, not a construction from the
actual digits or arithmetic of pi.  It rules out deriving natural-window
Fourier cancellation solely from the listed denominator, valuation, and
complete-spectrum facts.  It does not evaluate the target-weighted primitive
sum in T139, prove or refute the signed T148 premise, or say that the actual
pi carrier is coherent.

Likewise, the related stable-stencil consequence of T168 must remain
prime-local.  If an old `p^e` component is stable and the stencil polynomial
is `C`, then `v_p(C(10))=s<e` yields the exact valuation `s-e`.  In the
resonant branch `C(10)=0`, one obtains only p-integrality (`v_p >= 0`), not
the full reduced denominator or conductor of the rational stencil.

The source memo also contains a positive Euler--Machin carrier discussion
which is not promoted here as frontier progress.  Its equation (3.12) needs
the audit correction

\[
\frac{E_{239}}{E_5}<C<\frac23,
\]

not the displayed reversed inequalities.  That repair supports its
one-sided approximation calculation but does not change this no-go or supply
the missing pi-specific, target-signed estimate.

## Addendum: the literal pure-13 correction is coherent

Status: `proof sketch`

Source: `workflows/state/chatgpt-pro/20260825-open-frontier-creative-be/turns/0006/answer.md`,
with the zero-frequency and scope corrections below.

Let `M_m` be the accelerated rational Euler--Machin carrier from the existing
intermediate note, put

\[
 \delta_m=\pi-M_m,\quad
 A_m=\lfloor13^m\pi\rfloor,\quad
 L_m=\lfloor13^m\delta_m\rfloor,\quad
 W_m=\lfloor13^mM_m\rfloor,
\]

and let `U_m=W_m+epsilon_m`, where `epsilon_m` is `1` exactly when `13`
divides `W_m`, and is `0` otherwise.  Comparing the two fractional parts in
`13^m pi-13^m delta_m` gives `kappa_m in {0,1}` and hence the exact identity

\[
 \boxed{U_m=A_m-L_m+\sigma_m},
 \qquad \sigma_m=\epsilon_m-\kappa_m\in\{-1,0,1\}.
\tag{15}
\]

If `b_m=A_(m+1)-13A_m` is the next base-13 digit of pi, subtraction at two
successive depths gives the corresponding temporal identity

\[
 U_{m+1}-13U_m
 =b_m-(L_{m+1}-13L_m)+(\sigma_{m+1}-13\sigma_m).
\tag{16}
\]

This is an exact digit/carry decomposition, not a closed recurrence for the
unknown pi digits.

For the phase comparison, set

\[
 \gamma_m=\frac{L_m-\sigma_m}{13^m},\qquad
 \Omega_{h,n}=e(-h10^n\gamma_{k+n}),\qquad \Omega_{0,n}=1.
\]

Here `|gamma_m-delta_m|<2*13^(-m)`.  Combining this with the recorded
proof-sketch estimate `0<delta_m<K*10^(-m)*m^(-5/2)` shows that the literal
pure-13 phase is the base-13-prefix phase multiplied by `Omega_(h,n)`.  The
audited direct estimate must include frequency zero and use the Hermitian
product explicitly: for `k>=2`, every `N`, and
`0 <= h,l <= 2*10^k-1`,

\[
 \left|\sum_{n<N}\Omega_{h,n}\overline{\Omega_{\ell,n}}-N\right|
 =O(k^{-3/2})+O((10/13)^k),
\tag{17}
\]

uniformly in `N`.  Taking `ell=0` is the comparison actually needed for the
score; the source theorem's displayed positive-frequency range omitted this
case even though the same proof covers it.  Consequently, if

\[
 \mathcal L_{Q,A}=
 \sum_{u\in\operatorname{primitiveBoundarySupport}(Q)}
   |\operatorname{primitiveRayCoefficient}(Q,A,u)|,
 \]

then the complete target-signed primitive score of the pure-13 carrier differs
from the actual pi score by

\[
 \mathcal L_{Q,A}
 \bigl(O(k^{-3/2})+O((10/13)^k)\bigr),
\tag{18}
\]

again uniformly in the horizon.  This formulation uses the exact finite
coefficient load and does not rely on an unverified universal replacement.

The narrow consequence is that the Beatty/error correction alone is a
coherent translation and cannot be treated as an independent source of
cancellation.  The uncontrolled term is still the target-signed score of the
actual base-13 prefixes of pi.  This does **not** rule out using exact
unrounded rational arithmetic, finding another recurrence with compensating
terms, or introducing genuinely new pi-specific input.  It proves no T139 or
T148 premise, no cylinder hit, and no V1 statement.
