# T11: Autocorrelation viability audit for the T10 resonance

Status: `proof sketch` (rigorous prose note; no Lean artifact is claimed).

## 1. Scope, provenance, and immutable target

This note audits one route under the **literal failure** of canonical C1. It
does not prove or disprove C1. The canonical statement is the locally
formulated problem
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`; it records no external
source URL to preserve. Its checked SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

Canonical C1 says that there are one real `eta > 0` and one integer `N >= 1`
such that, for every integer `n >= N`,

```text
p_pi(n) >= 10^(eta*n).
```

The quantifier negation used below is therefore

```text
for every eta > 0 and every N >= 1, there is an n >= N such that
p_pi(n) < 10^(eta*n).
```

No scale-dependent `eta`, infinitely-often substitute, aligned-block
variant, or finite-prefix variant is used.

The accepted T10 artifact is
`knowledge_library/t10/T10ScaleAdaptiveOrbitFourier.lean`, SHA-256

```text
390946b9d5bc2f3d964b28eb98293db7c3268ad3dfe90aad2f75d4fef37fb4b8
```

The theorem used is
`piFailureC1_implies_arbitrarily_large_scale_resonance`, lines 435--456.

## 2. Normalization and T10's exact quantifiers

Write

```text
e(x) = exp(2*pi*i*x)
```

and, for an integer `h` and integer `M >= 0`, define

```text
S_h(M) = sum_{0 <= j < M} e(h*10^j*pi).
```

Thus `S_h(0)=0`. T10's `piOrbitSum h M` evaluates the same sum using the
fractional orbit `frac(10^j*pi)`. Since `h` is an integer and `e` has period
one,

```text
e(h*frac(10^j*pi)) = e(h*10^j*pi),
```

so its norm is exactly `|S_h(M)|`.

Assume literal failure of C1. T10 says, with the order of quantifiers retained,

```text
for every real B >= 0,
for every integer N >= 1,
there exist integers n,k,M,H >= 0 and h in Z such that
  N <= n,
  M = 10^n,
  4^k <= M,
  H = floor(M/2^(k+1)),
  h != 0,
  |h| < H,
  B*M < |S_h(M)|^2.
```

Here `|h|` is the natural absolute value. In particular `M >= 10`, because
`n >= N >= 1`. The witnesses `n,k,M,H,h` may depend on both `B` and `N`.
Crucially, `B` is chosen **before** the existentially supplied `M`; T10 gives
no upper bound for `M` in terms of `B`. The elementary upper bound
`|S_h(M)| <= M` only gives the posterior relation `B < M` for a T10 witness.

## 3. Exact finite autocorrelation identity

Let `M >= 1` and `h in Z`. Expanding the square gives

```text
|S_h(M)|^2
 = sum_{0 <= j,l < M} e(h*(10^j-10^l)*pi).
```

There are exactly `M` diagonal pairs `j=l`, each contributing one. For an
upper-diagonal pair write `j=l+r`, where the indexing conditions are exactly

```text
1 <= r < M,       0 <= l < M-r.
```

Its contribution is

```text
e(h*(10^(l+r)-10^l)*pi)
 = e(h*(10^r-1)*10^l*pi).
```

Summing over `l=0,...,M-r-1` gives

```text
S_{h*(10^r-1)}(M-r).
```

For the corresponding lower-diagonal pair `l=j+r`, the contribution is the
complex conjugate of the upper-diagonal contribution. Every off-diagonal
ordered pair occurs in exactly one of these two classes. Hence

```text
|S_h(M)|^2
 = M + sum_{1 <= r < M}
       (S_{h*(10^r-1)}(M-r)
        + conjugate(S_{h*(10^r-1)}(M-r)))
 = M + 2*Re(sum_{1 <= r < M} S_{h*(10^r-1)}(M-r)).       (3.1)
```

This proves the requested identity, including the zero-based indexing and the
length `M-r`.

## 4. Fixed truncation and all constants

Fix an integer `R` with `1 <= R <= M-1`. Put

```text
P_R = Re(sum_{1 <= r <= R} S_{h*(10^r-1)}(M-r)),
T_R = Re(sum_{R < r < M} S_{h*(10^r-1)}(M-r)).
```

Every summand in a sum of length `M-r` has modulus one, so

```text
|S_{h*(10^r-1)}(M-r)| <= M-r.
```

The discarded tail therefore satisfies

```text
|T_R|
 <= sum_{r=R+1}^{M-1} (M-r)
  = sum_{s=1}^{M-R-1} s
  = (M-R-1)*(M-R)/2.                                    (4.1)
```

The empty tail at `R=M-1` is covered by the same formula. From (3.1),

```text
P_R = (|S_h(M)|^2-M)/2 - T_R
    >= (|S_h(M)|^2-M-(M-R-1)*(M-R))/2.                  (4.2)
```

A maximum is at least the average of the `R` real numbers in `P_R`.
Consequently there is an integer `r` with `1 <= r <= R` such that

```text
Re S_{h*(10^r-1)}(M-r)
 >= L_R(h,M),                                            (4.3)

L_R(h,M)
 = (|S_h(M)|^2-M-(M-R-1)*(M-R))/(2*R).
```

In particular, without a sign assumption,

```text
max_{1 <= r <= R} |S_{h*(10^r-1)}(M-r)|
 >= max(0,L_R(h,M)).                                     (4.4)
```

This is the strongest bound asserted here from the exact identity plus only
the termwise bound `|S_q(L)| <= L`; no cancellation has been inserted into
the discarded tail.

For a T10 witness with `B*M < |S_h(M)|^2`, (4.2)--(4.3) become the strict
bound

```text
there is 1 <= r <= R such that

Re S_{h*(10^r-1)}(M-r)
 > Lambda_R(B,M),                                        (4.5)

Lambda_R(B,M)
 = (B*M-M-(M-R-1)*(M-R))/(2*R)
 = (M*(B-M+2*R)-R*(R+1))/(2*R).                         (4.6)
```

For a preassigned fixed `R`, positivity would require

```text
M*(B-M+2*R) > R*(R+1).                                  (4.7)
```

T10 does not imply (4.7): `B` precedes `M`, and there is no conclusion that
the later witness satisfies `M < B+2*R`. Thus the strongest fixed-short-range
bound furnished by this truncation can be negative and hence vacuous as a
modulus lower bound.

## 5. The full-range special-frequency consequence

It is useful to record exactly what remains if short-range control is
abandoned. Taking `R=M-1` in (4.5) makes the tail zero and gives, for every
`B>=0`,

```text
there is 1 <= r < M such that

Re S_{h*(10^r-1)}(M-r)
 > (B-1)*M/(2*(M-1)).                                    (5.1)
```

This choice of `R` is made after `M` is known; it is not a fixed short
truncation.

The quantifiers can be displayed without asymptotic notation. Given any real
`C >= 0` and integer `N >= 1`, apply T10 with

```text
B = 2*C+1.
```

Then T10 supplies its witnesses at some `n >= N`, and (5.1) supplies an
integer `r` with `1 <= r < M` for which

```text
Re S_{h*(10^r-1)}(M-r)
 > C*M/(M-1)
 >= C.                                                    (5.2)
```

The derived frequency is nonzero because `h != 0` and `10^r-1 > 0`.
Therefore literal failure of C1 does imply arbitrarily large **absolute**
special-frequency sums at arbitrarily late original scales. Formula (5.2) is
not a normalized resonance: T10 does not control `r`, the remaining length
`M-r`, or the ratio of the new sum to that length. Nor does it place
`h*(10^r-1)` in a T10 bandwidth at the new length.

## 6. Exact coherence premise missing from the route

The fixed-`R` obstruction is exactly the uncontrolled tail in (4.2), not an
unspecified need for "more cancellation." For fixed `R >= 1` and
`0 < delta <= 1`, define the following one-step short-lag coherence inequality
at a pair `(q,L)` with `L>R` and `|S_q(L)|^2>L`:

```text
Re(sum_{R < r < L} S_{q*(10^r-1)}(L-r))
 <= (1-delta)*(|S_q(L)|^2-L)/2.                          (COH)
```

Combining `(COH)` with (3.1), with `h=q` and `M=L`, gives

```text
Re(sum_{1 <= r <= R} S_{q*(10^r-1)}(L-r))
 >= delta*(|S_q(L)|^2-L)/2,
```

and hence some `1 <= r <= R` obeys

```text
Re S_{q*(10^r-1)}(L-r)
 >= delta*(|S_q(L)|^2-L)/(2*R).                         (6.1)
```

Thus `(COH)` is an exact sufficient replacement for the quadratic trivial
tail in (4.1).

For genuine multiscale amplification, the needed premise is also explicit:
there must be fixed `R` and `delta`, independent of the T10 scale, such that
`(COH)` holds not just at the initial T10 pair but successively at descendants

```text
q_{t+1} = q_t*(10^(r_t)-1),
L_{t+1} = L_t-r_t,             1 <= r_t <= R,            (6.2)
```

where `r_t` is chosen to satisfy (6.1). To continue at step `t+1`, one also
needs the checkable growth condition

```text
[delta*(|S_{q_t}(L_t)|^2-L_t)/(2*R)]^2 > L_t-r_t,       (6.3)
```

which ensures `|S_{q_{t+1}}(L_{t+1})|^2>L_{t+1}`. If the
descendants are to remain inside T10-style scale-adaptive estimates rather
than merely support another algebraic identity, one additionally needs an
nonnegative integer `k_{t+1}` satisfying

```text
4^(k_{t+1}) <= L_{t+1},
0 < |q_{t+1}| < floor(L_{t+1}/2^(k_{t+1}+1)).           (6.4)
```

For clarity, a fully quantified version of the coherent multiscale premise
for arbitrary finite depth is:

```text
there exist R >= 1 and 0 < delta <= 1 such that
for every real B > 1 and integers N,D >= 1,
there is a T10 witness (n,k_0,M,H_0,q_0) for (B,N), integers
r_0,...,r_(D-1), and nonnegative integers k_1,...,k_D such that,
recursively for 0 <= t < D,
  L_0=M,
  1 <= r_t <= R < L_t,
  q_(t+1)=q_t*(10^(r_t)-1),
  L_(t+1)=L_t-r_t,
  (COH) holds at (q_t,L_t),
  r_t satisfies (6.1),
  (6.3) holds,
  and (6.4) holds with the quantified integer k_(t+1).
                                                               (CM)
```

The coherent multiscale premise needed by this route is precisely `(CM)`;
its substantive new inequality is the descendant-stable `(COH)`. T10
supplies none of these descendant conditions. They are hypotheses, not
conclusions of this audit. If only algebraic iteration is wanted, omitting
the final (6.4) clause defines a weaker premise, but that weaker premise does
not retain T10-style bandwidth relevance.

## 7. Checked finite counterexample to coherence from one large sum

The failure is already combinatorial. For an abstract unit-circle sequence
`z_0,...,z_{M-1}`, set

```text
Z = sum_{j=0}^{M-1} z_j,
C_r = sum_{j=0}^{M-r-1} z_{j+r}*conjugate(z_j).
```

The same indexing proof gives `|Z|^2=M+2*Re(sum_{r=1}^{M-1}C_r)`.

Take the explicit finite sequence of length 12

```text
(z_0,...,z_11) = (1,1,-1, 1,1,-1, 1,1,-1, 1,1,-1).
```

Every entry has modulus one. Directly,

```text
Z = 4,                    |Z|^2 = 16 > 12,
C_1 = -3.
```

For a complete check, its real correlations `C_1,...,C_11` are

```text
-3, -4, 9, -2, -3, 6, -1, -2, 3, 0, -1.
```

They sum to `2`, and indeed `12+2*2=16`. At `R=1`, the discarded tail is

```text
C_2+...+C_11 = 5,
```

whereas `(|Z|^2-M)/2=2`. Thus `(COH)` would demand
`5 <= 2*(1-delta) < 2` for every `delta>0`, which is false. The one available
short correlation is not merely small; it is negative.

This is not a small-size accident. Repeating `(1,1,-1)` exactly `q` times
gives a finite sequence with

```text
M=3*q,       Z=q,       |Z|^2=q^2,       C_1=-(q-1).
```

For any preassigned real `B>=0`, choosing an integer `q>3*B` gives
`|Z|^2>B*M` while `C_1<0`.

More strongly, this same finite family defeats every preassigned short range
and coherence constant. Fix `R>=1` and `0<delta<=1`, and then choose an
integer

```text
q > max(3*B, 3+6*R/delta).                               (7.1)
```

For `P_R=Re(C_1+...+C_R)`, the trivial bound on each finite correlation gives

```text
P_R <= |P_R| <= sum_{r=1}^R |C_r| <= 3*R*q.              (7.2)
```

Here the energy excess is

```text
E=(|Z|^2-M)/2=(q^2-3*q)/2.
```

The second inequality in (7.1) is exactly `6*R < delta*(q-3)`, so

```text
3*R*q < delta*E.                                         (7.3)
```

By the identity, the discarded tail is `T_R=E-P_R`.
Inequality `(COH)` is equivalent to `P_R>=delta*E`, contradicting
(7.2)--(7.3). Thus, for every fixed `R` and positive `delta`, there are finite
unit-circle sequences satisfying the one-large-sum inequality with
arbitrarily large preassigned `B` but violating `(COH)` at that `R,delta`.

This counterexample does not assert that the pi orbit has this pattern; it
proves that the autocorrelation identity and one large sum alone cannot
establish `(COH)` or the existential fixed-`R,delta` premise `(CM)`.

## 8. Reused adjacent irrationality-measure audit

No source work is repeated here. The accepted bounded literature audit is
`knowledge_library/t5/DELTA_AUDIT.md`, SHA-256

```text
93089b4f44db9e295d1f8f560adf5b5b2922e624abfd084b92f6cfb8a0543129
```

Its source manifest records the accepted adjacent pi-positive-lower-block-
density T24 audit under SHA-256
`fedbf2ae2f990ddd57442d240989f878be9db1868a0fde9b85534572cdfab0bd`,
specifically for the exact irrationality-measure substitution and its
aggregate-energy limitation. It also pins the retained Zeilberger--Zudilin
PDF at

```text
3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5
```

The accepted conclusion reused here is narrow: the finite irrationality
measure for pi gives individual rational separation, but no aggregate
pair-sparsity, Fourier cancellation, or coherent autocorrelation bound. In
particular it does not imply `(COH)`, (6.3), or (6.4). This note makes no new
claim about the source theorem and does not promote that individual
separation into a collective estimate.

## 9. Numbered viability comparison and verdict

1. **Identity: SUFFICIENT and proved in finite form.** Equation (3.1) is exact;
   all diagonal, upper-diagonal, and lower-diagonal indices are accounted for.

2. **Fixed truncation: INSUFFICIENT.** The strongest stated bound from the
   identity and trivial tail is (4.5)--(4.6). For fixed `R`, T10's quantifier
   order does not force its positivity condition (4.7).

3. **Full-range extraction: TRUE BUT INSUFFICIENT.** Equations (5.1)--(5.2)
   produce arbitrarily large absolute special-frequency sums, but with
   uncontrolled `r`, remaining length, normalized size, and child bandwidth.

4. **Irrationality-measure input: INSUFFICIENT BY THE ACCEPTED AUDIT.** It is
   individual separation and does not provide the collective inequalities
   `(COH)`, (6.3), or (6.4).

5. **Final verdict: INSUFFICIENT.** T10's isolated resonance, the exact
   autocorrelation identity, and the accepted irrationality-measure input do
   not yield coherent arithmetic amplification or a contradiction to literal
   failure of C1. The precise additional hypothesis is the descendant-stable
   short-lag tail inequality `(COH)`, together with the explicit continuation
   and admissibility conditions (6.3)--(6.4). Section 7 proves by a checked
   finite unit-circle family that `(COH)` does not follow from one large sum.

## 10. Explicit gap ledger

- **GAP 1 (unproved):** `(COH)` for the fixed-pi lacunary phases, uniformly at
  a fixed `R` and positive `delta`.
- **GAP 2 (unproved):** persistence of enough energy for (6.3) at successive
  descendants.
- **GAP 3 (unproved):** scale-adaptive frequency admissibility (6.4) for the
  multiplicatively enlarged descendant frequencies.
- **GAP 4 (not supplied by the reused literature):** any aggregate
  irrationality estimate converting such a descendant chain into a
  contradiction.

No unconditional estimate for pi and no entropy conclusion is claimed.
