# Exact predecessor-digit DFT frontier

Status: `machine-checked` in T177 and T179. No one-sided estimate for a
prescribed nonzero sector is proved.

Date: 2026-08-27 UTC

## Exact decomposition

For the ten left children `A+dq`, define

\[
 C_r(q,A,N)=\sum_{d=0}^9 e(rd/10)
 Z^\pi_{10q,A+dq}(N),\qquad 0\le r<10.
\]

T177 proves the exact inverse transform

\[
 Z^\pi_{10q,A+dq}(N)
 =\frac1{10}\sum_{r=0}^9e(-rd/10)C_r(q,A,N). \tag{1}
\]

The sign convention is checked: the positive character in `C_r` selects fine
frequencies congruent to `r` modulo ten; inversion uses the negative
character.

The zero sector is literally T172:

\[
 C_0(q,A,N)=Z^\pi_{q,A}(N)+R^\pi_{q,A}(N). \tag{2}
\]

For a specified digit set

\[
 \Xi_{q,A,d}(N)=
 \Re\sum_{r=1}^9e(-rd/10)C_r(q,A,N).
\]

Then T177 machine-checks

\[
 10\Re Z^\pi_{10q,A+dq}(N)
 =\Re C_0(q,A,N)+\Xi_{q,A,d}(N), \tag{3}
\]

and the exact mean-zero law

\[
 \sum_{d=0}^9\Xi_{q,A,d}(N)=0. \tag{4}
\]

Consequently some digit has `Xi >= 0`. This is the exact character form of
the existential T172/Bellman selector.

## What this isolates

Equations (1)--(4) retain the complete primitive score and every target phase.
They do not average the desired child away: all nine pieces missing from the
zero-character transport are named explicitly.

The result also proves a tight negative boundary. Parent score, coefficient
positivity, defect mass, and the zero-sector Bellman surplus can guarantee one
maximizing child, but cannot determine a prescribed digit. That requires a
one-sided actual-pi estimate for its particular `Xi`.

T179 now machine-checks the corresponding actual-pi expansion. With

\[
 a_n=\lfloor 10x_n\rfloor,\qquad x_n=\{10^n\pi\},
\]

it first proves the exact decimal recurrence

\[
 x_n=\frac{a_n+x_{n+1}}{10},\qquad 0\le a_n<10.
\]

For every `1 <= r < 10`, it then proves

\[
 C_r(q,A,N)=\sum_{n<N}e(ra_n/10)\,
 H_{q,r}\!\left(x_{n+1}-c_{q,A}\right), \tag{5}
\]

where `H_{q,r}` is the explicit finite kernel retaining the literal T139
coefficients at frequencies `10 ell + r`. Thus the nonzero sectors are no
longer an informal "digit phase" heuristic: they are exact lag-one
predecessor-digit/suffix correlations for the actual decimal orbit of pi.
Equation (5) is an identity, not a cancellation or sign estimate.

## Next atomic rung

Prove or sharply falsify, for a named scale, target, and prescribed digit, a
one-sided bound for the explicit correlations in (5), strong enough after the
nine-character recombination to control `Xi_{q,A,d}`. Its sign must come from
the actual predecessor digits jointly with their next suffixes. A zero-sum
argument, unsigned energy estimate, target symmetry, rational shadow, or
coefficient-only calculation cannot supply this information.
