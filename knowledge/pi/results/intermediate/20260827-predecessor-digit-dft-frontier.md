# Exact predecessor-digit DFT frontier

Status: `machine-checked` in T177. No one-sided estimate for a prescribed
nonzero sector is proved.

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

The corresponding Pro derivation expands each `r != 0` sector into singleton
primitive frequencies and a lag-one predecessor-digit/suffix-phase
correlation. That further formula remains a `proof sketch`; T177 deliberately
formalizes only the DFT facts needed to state the gap without ambiguity.

## Next atomic rung

Prove or sharply falsify, for a named scale, target, and prescribed digit, a
lower bound for `Xi_{q,A,d}` whose sign comes from the actual decimal orbit of
pi. A zero-sum argument, unsigned energy estimate, target symmetry, rational
shadow, or coefficient-only calculation cannot supply this information.
