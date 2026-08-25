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
