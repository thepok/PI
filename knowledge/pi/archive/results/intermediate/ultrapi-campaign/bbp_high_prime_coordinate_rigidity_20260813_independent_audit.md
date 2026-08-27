# Independent audit: BBP high-prime coordinate rigidity

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local source supplies no external URL, so none is invented.

Frozen objects audited:

- [bbp_high_prime_coordinate_rigidity_20260813.md](bbp_high_prime_coordinate_rigidity_20260813.md),
  SHA-256
  `419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42`;
- [bbp_high_prime_coordinate_rigidity_20260813_check.py](bbp_high_prime_coordinate_rigidity_20260813_check.py),
  SHA-256
  `b80afdebbcb75b4c45a30a11fb3f8cf618119124d4354c637e559730bf3ef157`.

## Verdict and claim boundary

**PASS**, with two nonfatal corrections made explicit below. I independently
rederived the exact lattice identity, the cofactor estimate, and the
asymptotic uniqueness comparison.  The result has status `proof sketch`:

> For all sufficiently large depths `M`, retaining the full dyadic
> coordinate and the additive coordinates at every actual prime `p > M` in
> the reduced odd denominator forces all shadows onto a lattice of mesh
> `1/(16 C_M)`, with `log C_M ≤ M + o(M)`. Consequently the only such
> shadow lying within the certified BBP error radius of pi is `B_M`.

The finite replay has status `experiment`.  This statement neither estimates
the short decimal orbit of the surviving `B_M` nor proves the fixed-sixteen
return.  Canonical V1 therefore remains a `conjecture`.  Nothing in this audit
is `machine-checked`, a `candidate resolution`, or a `verified resolution`.

The only wording that needs care is the sentence in Section 2 of the primary
report saying that `p² > 8M+5` makes the exponent of `p > M` equal to one.
That inequality alone is not enough, because a prime could in principle occur
in two different linear factors at the same index.  The pairwise-resultant
fact proved in Section 3 supplies the missing simultaneous-factor exclusion.
With those two facts used together, the claim is correct; this is not a fatal
gap.

Also, the equality sign in the primary report's display (15) is stronger than
what (14) proves. From `log C_M ≤ M + o(M)` one gets the lower bound
`1/(16 C_M) ≥ exp(-(1+o(1))M)`, not an asymptotic equality. The uniqueness
argument uses only this lower bound, so displays (18)--(19) and the branch
verdict remain valid.

## 1. Exact hypotheses and CRT lattice

At a fixed sufficiently large depth write the reduced BBP sum as

\[
 B_M=\frac{P_M}{2^{K_M}R_M},\qquad
 (P_M,2R_M)=1,\quad R_M\text{ odd},\qquad
 D_M=2^{K_M-4}.
\]

Thus (B_M=P_M/(16D_MR_M)).  Let (w_M) be the unique integer in
([0,D_M)) satisfying

\[
 w_M\equiv P_MR_M^{-1}\pmod {D_M},
\]

and put

\[
 c_M=\frac{P_M-R_Mw_M}{D_M}.
\]

The congruence makes (c_M) integral, and direct substitution gives

\[
 16B_M=\frac{w_M}{D_M}+\frac{c_M}{R_M}.             \tag{A1}
\]

Moreover (c_MD_M\equiv P_M\pmod {R_M}).  Both (D_M) and (P_M)
are units modulo every prime dividing (R_M), so
((c_M,R_M)=1).

Define precisely

\[
 S_M=\prod_{\substack{p>M\\p\mid R_M}}p,
 \qquad C_M=R_M/S_M.                                \tag{A2}
\]

For sufficiently large (M), every prime in (S_M) is greater than five,
has exponent exactly one in (R_M), and occurs in no other part of (C_M).
Hence

\[
 R_M=S_MC_M,\qquad (S_M,C_M)=1.                    \tag{A3}
\]

For each (p\mid S_M), (R_M/p) is a unit modulo (p), so the retained
additive coordinate is well-defined as

\[
 \gamma_{M,p}(c)=c(R_M/p)^{-1}\pmod p.             \tag{A4}
\]

The preservation hypothesis is exactly
(gamma_{M,p}(c'_M)=gamma_{M,p}(c_M)) for every (p\mid S_M), with the
same ambient odd denominator (R_M) and the same dyadic coordinate (w_M).
Multiplying (A4) by the unit (R_M/p) shows that this is equivalent to
(c'_M\equiv c_M\pmod p).  The factors of (S_M) are distinct, so CRT gives
the biconditional

\[
 \bigl(\forall p\mid S_M:\gamma_{M,p}(c'_M)=\gamma_{M,p}(c_M)\bigr)
 \quad\Longleftrightarrow\quad
 c'_M=c_M+S_Mt\quad(t\in\mathbb Z).                 \tag{A5}
\]

For

\[
 X_M(c')=\frac{R_Mw_M+D_Mc'}{16D_MR_M},            \tag{A6}
\]

(A1)--(A5) yield, without an approximation,

\[
 X_M(c'_M)-B_M
 =\frac{D_MS_Mt}{16D_MR_M}
 =\boxed{\frac{t}{16C_M}}.                         \tag{A7}
\]

Thus a distinct coordinate-preserving shadow is separated from (B_M) by
at least (1/(16C_M)).  The factor (16) is essential and has not been
dropped.

## 2. Why the high primes have exponent one

Every odd denominator prime comes from one of

\[
 2k+1,\quad4k+3,\quad8k+1,\quad8k+5,qquad0\le k\le M,
\]

whose values are at most (X=8M+5).  The six absolute determinants of the
corresponding affine forms are

\[
 2,\ 6,\ 2,\ 20,\ 4,\ 32.                          \tag{A8}
\]

Any prime dividing two forms at the same integer (k) divides their
determinant.  Therefore no prime (p>5) divides two pole factors at the same
index.  If also (p>M), then eventually (p^2>X), so (p) cannot occur
twice in the one factor it may divide.  The odd denominator of each summand,
and hence its least common multiple and the reduced denominator (R_M), has
(p)-valuation at most one.  Since (p\mid R_M), that valuation is exactly
one.  This proves (A3) and validates the inverse in (A4).

Notice the quantifier: only **actual surviving** primes (p\mid R_M) enter
(S_M).  A possible pole prime cancelled before reaching the reduced
denominator supplies no retained coordinate and is not silently reinserted.

## 3. Small-prime and prime-power cofactor bound

Let (L_M) be the least common multiple of the odd pole products through
depth (M).  Adding reduced rational summands cannot create a denominator
prime power absent from (L_M), so (R_M\mid L_M).  After removing (S_M),
all prime divisors of (C_M) are at most (M).

For (p>5), (A8) shows that at most one pole factor at a fixed (k) is
divisible by (p).  Since each pole is at most (X),

\[
 v_p(C_M)\le\lfloor\log_pX\rfloor.                 \tag{A9}
\]

For (p=3,5), allowing all four factors gives the safe estimate

\[
 v_p(C_M)\le4\lfloor\log_pX\rfloor.                \tag{A10}
\]

There is no (p=2) contribution because (R_M) and (C_M) are odd.  On
expanding the floors as counts of prime powers, (A9)--(A10) give

\[
 \log C_M
 \le \vartheta(M)
   +\sum_{\ell\ge2}\vartheta(X^{1/\ell})+O(\log M). \tag{A11}
\]

The fixed factors 3 and 5 account for the `O(log M)` correction. The
prime number theorem gives `θ(M) = M + o(M)`, while a Chebyshev bound
gives

\[
 \sum_{\ell\ge2}\vartheta(X^{1/\ell})
 =O(\sqrt M\log M)=o(M).
\]

Consequently

\[
 \boxed{\log C_M\le M+o(M)}.                       \tag{A12}
\]

This is an upper bound on the unpreserved cofactor.  It correctly implies a
lower bound (exp(-(1+o(1))M)/16) on lattice spacing; it does not imply that
the selected residue is equidistributed.

## 4. BBP tail and the uniqueness threshold

For the positive BBP coefficient

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},
\]

one has `0 < a(k) ≤ 1/k²` for `k ≥ 1`: after clearing the positive
denominator, the difference is

\[
 392k^4+873k^3+665k^2+194k+15>0.
\]

The BBP identity therefore gives

\[
 0<\pi-B_M
 \le\frac1{(M+1)^2}\sum_{k=M+1}^{\infty}16^{-k}
 =\frac{16^{-M}}{15(M+1)^2}=:E_M.                  \tag{A13}
\]

If a coordinate-preserving (X_M(c'_M)) also obeys
(|X_M(c'_M)-\pi|\le E_M), then

\[
 |X_M(c'_M)-B_M|\le2E_M.                           \tag{A14}
\]

The logarithm of the ratio between the nonzero lattice spacing and this
two-tail radius is exactly

\[
 \log\frac{1/(16C_M)}{2E_M}
 =M\log16-\log C_M+2\log(M+1)+\log(15/32).         \tag{A15}
\]

By (A12), its leading coefficient is at least
(log16-1-o(1)>0).  Hence it tends to (+infty), so eventually

\[
 2E_M<\frac1{16C_M}.                                \tag{A16}
\]

Equations (A7), (A14), and (A16) force (t=0), and therefore
(X_M(c'_M)=B_M).  This proves the claimed asymptotic uniqueness at BBP
scale.

## 5. Stress tests

- **Cancelled potential primes.**  Only primes in the actual reduced
  (R_M) are constrained.  Nothing in the proof assumes that every pole
  prime survives reduction.
- **Cancellation in an alternative shadow.**  For (p\mid S_M), the
  congruence (c'_M\equiv c_M\not\equiv0\pmod p) prevents cancellation of
  a retained prime.  Small primes in (C_M) may cancel.  Formula (A7) is an
  equality of rationals before or after reduction, so such cancellation is
  harmless.
- **Prime powers.**  High primes have exponent one by Section 2.  All powers
  of primes at most (M) remain in (C_M) and are bounded by (A9)--(A10);
  no preservation of their coordinates is assumed.
- **Fixed primes (2,3,5).**  The factor (2) is isolated in (16D_M).
  Since (w_M) is odd and (D_M) is even, the numerator in (A6) is odd, so
  no dyadic cancellation occurs.  Primes (3,5) receive the four-factor
  allowance (A10).
- **Reduced versus ambient denominators.**  The starting (R_M) is reduced.
  Alternative shadows use the same ambient denominator, but may reduce by a
  factor of (C_M).  This changes neither the CRT implication nor (A7).
- **The factor (16).**  It is present both in the mesh (1/(16C_M)) and in
  the final constant (15/32) in (A15).  Its constant contribution cannot
  alter the decisive exponent comparison (log16>1).

## 6. Disjoint exact replay

The independent checker
[bbp_high_prime_coordinate_rigidity_20260813_independent_check.py](bbp_high_prime_coordinate_rigidity_20260813_independent_check.py)
has SHA-256
`71cff87466f5169a226ad86fffc487e84f4e4e24ebcbb50478da45674147564d`.
It imports neither the primary checker nor `fractions.Fraction`; it uses
normalized integer pairs, reconstructs the BBP sums, builds the ambient odd
LCM, factors the actual reduced denominator, and tests four positive and
negative lattice shifts at every retained depth.

Replay from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_independent_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_independent_check.py \
      --max-depth 180

The retained run reports:

    status: PASS
    claim_label: experiment
    depths_checked: 169
    prime_exponent_bound_checks: 3879
    coordinate_preservation_checks: 53952
    lattice_spacing_checks: 676
    cofactor_cancellation_examples: 530
    observed_permanent_uniqueness_onset: 12
    minimum_log_spacing_over_two_tail: 23.74023712965329
    final_log_cofactor_over_depth: 1.067310470830356
    asserts_fixed_sixteen_return: false
    asserts_v1: false

The 530 sampled small-prime cancellations directly stress the claim that
reduction of an alternative shadow is harmless.  The finite onset and ratios
remain only an `experiment`; the asymptotic result is the `proof sketch` in
Sections 1--4.

## 7. Coordination record

This audit registered the descendant-area watch
`ultrapi-high-prime-rigidity-audit-20260813` on `local:pi-digits` for agent
`codex-ultrapi-high-prime-rigidity-audit`. The initial and final polls were
empty at cursor and delivered sequence 56,949. Observation events are
coordination signals only and were not used as mathematical evidence. Since
no event was delivered, there was no sequence to acknowledge.

## Final assessment

The audited mechanism is genuinely closed: once all selected high-prime
coordinates and the full dyadic coordinate are retained, the unpreserved
cofactor lattice is much coarser than the BBP transfer window, so no distinct
BBP-quality shadow exists eventually.  The unique surviving point is the
actual (B_M).  No argument here controls its synchronized short orbit, so
no fixed return and no V1 conclusion follows.
