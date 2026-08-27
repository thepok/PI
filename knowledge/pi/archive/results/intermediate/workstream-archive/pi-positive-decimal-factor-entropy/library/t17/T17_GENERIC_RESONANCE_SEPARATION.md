# T17: Generic resonance amplification separation

Claim status: `proof sketch` (a self-contained rigorous prose argument, not a
Lean-checked theorem).

## 1. Provenance and scope

The immutable canonical statement is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`. Its SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

The canonical file records a system formulation dated 2026-07-22 and no
external source URL. Its question concerns the decimal factor entropy of pi.
The result below instead concerns generic finite sign sequences. It is a
separation result serving G5, not a result about the canonical question or any
of its pi-specific siblings.

## 2. Normalized statement and quantifiers

For every integer `t >= 2`, put

\[
  N_t=t^6,\qquad S_t=t^4.
\]

There is a family, chosen once and for all,

\[
  (a^{(t)})_{t\geq 2},\qquad
  a^{(t)}=(a^{(t)}_0,\ldots,a^{(t)}_{N_t-1})
  \in\{-1,+1\}^{N_t},
\]

such that

\[
  \sum_{j=0}^{N_t-1}a^{(t)}_j=S_t
\]

and, for the aperiodic correlations

\[
  C_t(r)=\sum_{j=0}^{N_t-r-1}a^{(t)}_{j+r}a^{(t)}_j
  \quad (1\leq r<N_t),
\]

one universal explicit constant, namely `C=3`, satisfies

\[
  \sum_{r=1}^{N_t-1}|C_t(r)|^2\leq 3t^{12}.
  \tag{2.1}
\]

Define

\[
  B_t=\frac{\left|\sum_j a^{(t)}_j\right|^2}{N_t}=t^2,
  \qquad
  D_t=\left|\sum_j a^{(t)}_j\right|^2-N_t
      =N_t(B_t-1).
  \tag{2.2}
\]

For a natural-number cutoff `R`, define the absolute fraction of the
diagonal-subtracted correlation sum captured through that cutoff by

\[
  F_t(R)=
  \frac{\left|\sum_{1\leq r\leq \min(R,N_t-1)}C_t(r)\right|}{D_t/2}.
  \tag{2.3}
\]

Then, for every `t >= 2` and every natural `R`,

\[
  F_t(R)\leq \frac{2\sqrt{3R}}{B_t-1}.
  \tag{2.4}
\]

Consequently, **after the family has been chosen**, for every sequence of
natural cutoffs `(R_t)` satisfying

\[
  R_t=o(B_t^2),
  \quad\text{that is,}\quad \frac{R_t}{B_t^2}\longrightarrow 0,
\]

one has `F_t(R_t) -> 0` as `t -> infinity`.

The quantifier order is therefore

\[
  \exists (a^{(t)})_{t\geq2}\ \forall (R_t)_{t\geq2},
  \qquad
  R_t=o(B_t^2)\Longrightarrow F_t(R_t)\to0,
  \tag{2.5}
\]

not a cutoff-dependent choice of the sign sequences.

### Quantifier and normalization ambiguities resolved

1. Every occurrence of `t` means an integer `t >= 2`.
2. Correlations are aperiodic, with the full positive-lag range
   `1 <= r < N_t` and inner range exactly `0 <= j < N_t-r`.
3. A cutoff sequence is natural-valued. Formula (2.3) also covers `R=0` and
   `R >= N_t` without changing the lag definition.
4. "Captured fraction" refers to the signed correlation contribution in the
   exact autocorrelation identity, with an absolute value placed around the
   short sum. The denominator is `D_t/2`, exactly the T13 coherence
   normalization. Equivalently, one can double numerator and denominator and
   speak of a fraction of `D_t`.
5. `B_t` is the total normalized squared sum. The diagonal-subtracted
   normalized quantity is `B_t-1`; these are not interchangeable in any
   finite formula.
6. The `ZMod 2` Fourier transform below uses normalized averaging by `N_t`
   and the nontrivial character `x |-> (-1)^x`.

## 3. Fixed-composition probability space

Fix `t >= 2` temporarily and abbreviate `N=N_t` and `S=S_t`. Since `N` and
`S` have the same parity and `0 <= S <= N`, the integers

\[
  n_+=\frac{N+S}{2},\qquad n_-=\frac{N-S}{2}
\]

are nonnegative and sum to `N`. Let `Omega` be the finite, nonempty set of all
sign sequences with exactly `n_+` plus signs and `n_-` minus signs. Give
`Omega` the uniform measure. This is only a finite average over a specified
set; no independence, limiting random model, or probabilistic heuristic is
being assumed.

For distinct coordinate indices, permutation symmetry gives constants

\[
  \mu_2=\mathbb E[a_i a_j],\qquad
  \mu_4=\mathbb E[a_i a_j a_k a_\ell].
\]

They can be computed exactly. Every member of `Omega` has
`sum_i a_i=S` and `sum_i a_i^2=N`, so

\[
  \sum_{i\ne j}a_i a_j=S^2-N.
\]

There are `N(N-1)` ordered distinct pairs. Hence

\[
  \boxed{\mu_2=\frac{S^2-N}{N(N-1)}}.
  \tag{3.1}
\]

For completeness, let `e_q` be the `q`-th elementary symmetric polynomial in
the `N` signs. Their first four power sums are `S,N,S,N`. Newton's identities
give

\[
  e_1=S,\qquad 2e_2=S^2-N,
\]

\[
  3e_3=e_2S-e_1N+S,
  \qquad
  4e_4=e_3S-e_2N+e_1S-N.
\]

Substitution yields the deterministic identity

\[
  24e_4=S^4-(6N-8)S^2+3N^2-6N.
\]

The left side is the sum of `a_i a_j a_k a_l` over all ordered quadruples of
distinct indices. There are `N(N-1)(N-2)(N-3)` such quadruples, so

\[
  \boxed{\mu_4=
  \frac{S^4-(6N-8)S^2+3N^2-6N}
       {N(N-1)(N-2)(N-3)}}.
  \tag{3.2}
\]

These are exact fixed-composition moments. In particular, replacing them by
independent biased-sign moments would be incorrect.

## 4. Exact moment at every aperiodic lag

Fix any lag `r` with `1 <= r < N`, and put `m=N-r`. Expanding the square gives

\[
  C(r)^2=\sum_{0\leq j,k<m}
  a_{j+r}a_j a_{k+r}a_k.
\]

View each starting point `j` as the edge `{j,j+r}`.

1. There are exactly `m` ordered pairs with `j=k`; their products equal `1`.
2. Two distinct lag-`r` edges share an endpoint exactly when `k=j+r` or
   `j=k+r`. Thus the exact number of ordered overlapping pairs is

   \[
     q_r=2\max(m-r,0)=2\max(N-2r,0).
   \]

   Their products reduce to products at two distinct coordinates and have
   expectation `mu_2`.
3. The remaining

   \[
     d_r=m^2-m-q_r
   \]

   ordered pairs have four distinct endpoints and expectation `mu_4`.

Therefore, with no omitted lag range,

\[
  \boxed{\mathbb E[C(r)^2]
    =m+q_r\mu_2+d_r\mu_4}
  \qquad(1\leq r<N).
  \tag{4.1}
\]

This includes the long-lag range `ceil(N/2) <= r < N`, where `q_r=0`.

## 5. One universal constant

Here `N=t^6 >= 64` and `S=t^4`. Formula (3.1) shows `mu_2 >= 0`, and

\[
  \mu_2\leq \frac{S^2}{N(N-1)}
  \leq 2\frac{S^2}{N^2}=2t^{-4}.
  \tag{5.1}
\]

Also `N-k >= N/2` for `k=1,2,3`, so the denominator in (3.2) is at least
`N^4/8`. The triangle inequality applied to its exact numerator gives

\[
\begin{aligned}
  |\mu_4|
  &\leq 8\left(
       \frac{S^4}{N^4}
       +6\frac{S^2}{N^3}
       +\frac{3}{N^2}
       +\frac{6}{N^3}\right)\\
  &=8\left(t^{-8}+6t^{-10}+3t^{-12}+6t^{-18}\right)\\
  &\leq 8\left(1+\frac32+\frac3{16}+\frac3{512}\right)t^{-8}
   =\frac{1379}{64}t^{-8}
   <22t^{-8}.
\end{aligned}
  \tag{5.2}
\]

As `r` runs from `1` to `N-1`, the number `m=N-r` runs from `N-1` to `1`.
Moreover `q_r <= 2m` and `0 <= d_r <= m^2`. Consequently

\[
  \sum_r m=\frac{N(N-1)}2\leq\frac{N^2}{2},
  \qquad
  \sum_r q_r<N^2,
\]

and

\[
  \sum_r d_r\leq\sum_{m=1}^{N-1}m^2
   =\frac{(N-1)N(2N-1)}6<\frac{N^3}{3}.
\]

Using (4.1), `d_r >= 0`, and `mu_4 d_r <= |mu_4|d_r`, we obtain

\[
\begin{aligned}
  \mathbb E\sum_{r=1}^{N-1}|C(r)|^2
  &\leq \frac{N^2}{2}+2t^{-4}N^2
       +\frac{22}{3}t^{-8}N^3\\
  &\leq \left(\frac12+\frac18+\frac{11}{6}\right)N^2
   =\frac{59}{24}N^2
   <3N^2.
\end{aligned}
  \tag{5.3}
\]

The average of finitely many nonnegative values is less than `3N^2`, so at
least one member of `Omega` has total squared correlation at most `3N^2`.
Since `N^2=t^12`, this proves (2.1) with the single universal constant `C=3`.

To make the family-before-cutoff order literal, for each `t` choose the first
qualifying sequence in the lexicographic order with `-1 < +1`. This choice
depends only on `t` and the displayed finite criterion. It mentions no cutoff
`R` or cutoff sequence `(R_t)`.

## 6. The cutoff bound and the distinction between B_t and B_t-1

The elementary aperiodic autocorrelation identity for real signs is

\[
  \left|\sum_{j=0}^{N_t-1}a^{(t)}_j\right|^2
   =N_t+2\sum_{r=1}^{N_t-1}C_t(r).
  \tag{6.1}
\]

Thus the diagonal-subtracted quantity is exactly

\[
  D_t=S_t^2-N_t=N_t(B_t-1)=N_t(t^2-1)>0,
  \tag{6.2}
\]

and the full positive-lag sum is `D_t/2`. In particular, the denominator in
T13's `ShortLagCoherence` is

\[
  \frac{\left|\sum_j a^{(t)}_j\right|^2-N_t}{2}
  =\frac{N_t(B_t-1)}2,
\]

not `N_t B_t/2`.

There are at most `R` terms in the numerator of (2.3). Cauchy-Schwarz and
(2.1) therefore give, for every natural `R`,

\[
\begin{aligned}
  \left|\sum_{1\leq r\leq\min(R,N_t-1)}C_t(r)\right|
  &\leq \sqrt{R}
       \left(\sum_{r=1}^{N_t-1}|C_t(r)|^2\right)^{1/2}\\
  &\leq \sqrt{3R}\,N_t.
\end{aligned}
\]

Dividing by `D_t/2` proves (2.4). If `R_t/B_t^2 -> 0`, then

\[
  \frac{\sqrt{R_t}}{B_t-1}
  =\sqrt{\frac{R_t}{B_t^2}}\frac{B_t}{B_t-1}
  \longrightarrow 0,
\]

because `B_t=t^2 -> infinity`. Hence `F_t(R_t) -> 0` for every such cutoff
sequence, after the common family has already been fixed.

## 7. Exact normalized ZMod 2 coefficient

Encode the signs by `x_j in ZMod 2` through

\[
  a^{(t)}_j=(-1)^{x_j};
\]

thus `x_j=0` represents `+1` and `x_j=1` represents `-1`. For the empirical
probability measure of these `N_t` points and the unique nontrivial character
`chi_1(x)=(-1)^x`, use the normalized Fourier convention

\[
  \widehat\mu_t(1)=\frac1{N_t}\sum_{j=0}^{N_t-1}\chi_1(x_j).
\]

The fixed composition gives the exact, nonzero value

\[
  \boxed{\widehat\mu_t(1)
    =\frac1{N_t}\sum_j a^{(t)}_j
    =\frac{S_t}{N_t}=t^{-2}.}
  \tag{7.1}
\]

There is no asymptotic error term and no choice of a favorable character:
`ZMod 2` has exactly one nonzero frequency.

## 8. Exact comparison with T10 and T13

The kernel-checked T10 file
`TheoryLib.PiPositiveDecimalFactorEntropy.T10T10ScaleAdaptiveOrbitFourier`
places the scalar threshold before its witnesses. Its contrapositive has the
prefix

\[
  \forall B\geq0\ \forall N_0\geq1\ \exists n,k,M,H,h
\]

and then imposes the decimal-orbit conditions, including `n >= N_0`,
`M=10^n`, an adaptive bandwidth, and a nonzero integer frequency. The present
family has only the analogous scalar fact

\[
  \forall B\geq0\ \forall T\geq2\ \exists t\geq T,
  \qquad B<B_t=t^2.
\]

This is the entire T10 comparison. The sign family does not supply any of
T10's other witnesses or compatibility conditions.

The kernel-checked T13 definition `ShortLagCoherence z M R delta` uses

\[
  (1-\delta)
  \frac{\left\|\sum_{j<M}z_j\right\|^2-M}{2}
\]

as its long-tail upper bound, and its retained conclusion is normalized by
the same diagonal-subtracted half-energy. Equations (6.1)-(6.2) compare to
that exact normalization. For this generic family, every
`R_t=o(B_t^2)` has absolute retained fraction tending to zero, despite
unbounded `B_t`, the exact finite-group coefficient (7.1), and the
baseline-order second-moment bound (2.1). Thus those three scalar data alone
cannot force a positive fixed fraction at such cutoffs.

## 9. Explicit nonclaims

This note does **not** assert or imply any of the following:

1. `N_t` or any sample size here equals `10^n`.
2. The signs arise from the decimal orbit `frac(10^j pi)`, decimal digits, or
   any circle orbit.
3. A lag operation on these `ZMod 2` codes produces T10's or T13's required
   descendant frequency, phase relation, bandwidth, or remaining-length
   compatibility.
4. The family satisfies or refutes the full hypotheses or conclusions of T10
   or T13.
5. Any unconditional statement about pi, C1, C2, C3, C4, C5, decimal factor
   entropy, or decimal word occurrence.

The separation is strictly generic: unbounded scalar resonance, an exact
finite-group coding coefficient, and an `O(N_t^2)` aperiodic lag second moment
do not by themselves amplify into short-lag coherence at every cutoff below
the `B_t^2` scale.
