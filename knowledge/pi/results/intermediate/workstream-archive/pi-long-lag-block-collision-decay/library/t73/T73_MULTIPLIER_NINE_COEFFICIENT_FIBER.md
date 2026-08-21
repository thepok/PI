# T73: exact multiplier-nine coefficient fiber

Claim label: `proof sketch` (the only imported mathematical input is the
kernel-checked T69 interface; the new finite algebra below is proved in prose
and is not machine-checked).

Date: 2026-08-03 UTC.

## 1. Provenance, normalized target, and scope

The canonical question is the locally formulated statement delivered
byte-for-byte as `CANONICAL_STATEMENT.txt`. It has no external source URL. Its
SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That question asks, for each real `0 < s < 1`, for one constant `C_s` before
all positive `m,N` in an ordered long-lag collision estimate at the prescribed
number `pi`. This note does not answer or modify that question. It concerns
only the residual A12, `m=1`, dyadic primitive-sector algebraic mechanism in
T69. In particular, none of the following is asserted here:

1. a fixed-`pi` estimate `(FP)`;
2. T69's aggregate hypothesis;
3. the full T29 width-weighted square-function predicate;
4. C3, C2, C1, or the canonical collision estimate.

The established input is the kernel-checked module

```lean
import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc
```

whose retained source has SHA-256

```text
09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301
```

Specifically, T69's theorem `aggregateEnergy_literal` supplies the finite sum
recalled in Section 2. No claim from the T70, T71, or T72 notes is used as a
premise. Those notes are only motivation; their verification level is
`proof sketch` or literature support rather than a kernel proof of the finite
classification below.

The quantifiers and possible ambiguities are fixed as follows.

1. The scale `t` is an arbitrary natural number.
2. Both frequency variables range over every integer from `1` through `10`.
3. Both shift variables satisfy `1 <= r,r' < H_t`.
4. Ordered channel pairs are retained; reversing a pair negates its Laurent
   character.
5. Unequal orbit lengths are intersected, never padded: the common endpoint is
   exactly `k < N_t-max(r,r')`.
6. A coefficientwise obstruction is not a lower bound after evaluation at
   `pi`, because distinct Laurent characters may still cancel there.

## 2. Literal T69 sum and independent double-shift reconstruction

Fix `t` and abbreviate

```text
N = N_t = 4*2^t+1,
H = H_t = ceil(sqrt(N)),
q(h,r) = h*(10^r-1),
w_r = H-r,
e(x) = exp(2*pi*i*x).
```

Since `N >= 5`, one has `H >= 3` and `H < N`. T69's literal off-diagonal
aggregate sum is

```text
A_t(pi)
  = sum_(h=1)^10 sum_(r=1)^(H-1) w_r
      sum_(k=0)^(N-r-1) e(q(h,r)*10^k*pi).               (2.1)
```

Its kernel-checked identity is

```text
aggregateEnergy(t) = 10*H*N + 2*Re A_t(pi).              (2.2)
```

Equation (2.1), including all domains and weights, is therefore imported from
T69. For an arbitrary real `alpha`, let `A_t(alpha)` denote the same finite
expression with the final prescribed phase `pi` in (2.1) replaced by `alpha`.
This is notation for the formal algebra only; no variable-phase estimate is
asserted. Everything from the following reindexing onward is reconstructed
here.

For a formal Laurent indeterminate `Z`, define

```text
B_k(Z) = sum_(h=1)^10
           sum_(1 <= r < H, k < N-r) w_r*Z^(q(h,r)*10^k).
                                                                    (2.3)
```

The union of the original `k` ranges is exactly `0 <= k <= N-2`, and
`k < N-r` is equivalent to `r <= min(H-1,N-k-1)`. Thus finite reindexing of
(2.1) gives

```text
A_t(alpha) = sum_(k=0)^(N-2) B_k(e(alpha)),              (2.4)
```

where `Z^n` evaluates as `e(n*alpha)`. Cauchy--Schwarz gives the dispersion
inequality

```text
|A_t(alpha)|^2 <= (N-1)*E_t(alpha),
E_t(alpha) = sum_(k=0)^(N-2) |B_k(e(alpha))|^2.          (2.5)
```

The formal Laurent polynomial evaluated by `E_t` is

```text
P_t(Z) = sum_(k=0)^(N-2) B_k(Z)*B_k(Z^(-1)).             (2.6)
```

Expanding (2.6), a channel `(h,r)` and a channel `(h',r')` are simultaneously
active precisely when

```text
k < min(N-r,N-r') = N-max(r,r').                        (2.7)
```

Consequently the literal ordered double-shift expansion is

```text
P_t(Z)
 = sum_(h=1)^10 sum_(h'=1)^10
    sum_(r=1)^(H-1) sum_(r'=1)^(H-1)
      (H-r)*(H-r')
      sum_(k=0)^(N-max(r,r')-1)
        Z^((q(h,r)-q(h',r'))*10^k).                     (2.8)
```

This proves rather than assumes the unequal-length cutoff requested in the
agenda item. Neither `N-r` nor `N-r'` is a uniformly correct asymmetric
choice: the former is correct only when `r=max(r,r')`, and the latter only
when `r'=max(r,r')`; the rectangular length `N` is always too long. Reversing
the ordered channels preserves the weight and cutoff and negates the exponent,
so `P_t` is invariant under `Z -> Z^-1`.

## 3. Exhaustive multiplier-nine tuple classification

We classify every tuple in the ambient domains satisfying

```text
q(h,r)-q(h',r') = epsilon*9*10^a,
epsilon in {+1,-1}, a >= 0.                              (3.1)
```

### Theorem 3.1 (complete list)

For `1 <= j <= 9` and `s >= 1`, all positive-orientation solutions are
exactly

```text
S   : (h,r;h',r';a) = (j+1,1; j,1; 0),                 (3.2)
C   : (h,r;h',r';a) = (1,s+1; 10,s; 0),                (3.3)
V_1 : (h,r;h',r';a) = (1,s+1; 1,s; s),                 (3.4)
V_10: (h,r;h',r';a) = (10,s+1; 10,s; s+1).             (3.5)
```

Here S is the same-shift family, C is the adjacent cross-frequency family,
and `V_1,V_10` are the two vertical families. In the finite T73 domain,
`1 <= s <= H-2` in C, `V_1`, and `V_10`. Every negative-orientation solution
is the reversal of exactly one displayed positive solution:

```text
(h,r;h',r';a) -> (h',r';h,r;a).                         (3.6)
```

There are no other solutions.

### Proof

Modulo `10`, since `10^r-1 == -1 (mod 10)`, one has

```text
q(h,r)-q(h',r') == h'-h (mod 10).                       (3.7)
```

First suppose `a >= 1`. The right side of (3.1) is zero modulo `10`.
The residues of `1,...,10` modulo `10` are distinct, so (3.7) forces `h=h'`.
After reversing the channels if necessary, assume the sign is positive and
write `r=s+delta`, where `s=r' >= 1` and `delta >= 1`. Equation (3.1) becomes

```text
h*10^s*(10^delta-1) = 9*10^a.                           (3.8)
```

The factor `10^delta-1` is coprime to `10`, so it divides `9`. It is at least
`9`, hence it equals `9` and `delta=1`. Cancelling `9` in (3.8) leaves

```text
h*10^s = 10^a.                                          (3.9)
```

For `1 <= h <= 10`, (3.9) has exactly the alternatives

```text
h=1,  a=s;      h=10, a=s+1.                            (3.10)
```

These are `V_1` and `V_10`, and reversal gives their negative orientations.

It remains to treat `a=0`. Again classify the positive sign; reversal will
give the negative sign. From (3.7),

```text
h'-h == 9 (mod 10),  -9 <= h'-h <= 9,                  (3.11)
```

so either `h'=h-1` or `(h,h')=(1,10)`.

If `h'=h-1`, direct expansion of `q(h,r)-q(h-1,r')=9` gives

```text
h*10^r-(h-1)*10^r' = 10.                                (3.12)
```

Therefore `10^min(r,r')` divides `10`, and `min(r,r')=1`. If `r>r'=1`,
division by `10` turns (3.12) into
`h*10^(r-1)-(h-1)=1`, hence `10^(r-1)=1`, a contradiction. If
`r'>r=1`, the same argument gives
`h-(h-1)*10^(r'-1)=1`, hence `10^(r'-1)=1`, also a contradiction.
Thus `r=r'=1`, and all nine choices `h=j+1,h'=j` give S.

If `(h,h')=(1,10)`, the equation is

```text
(10^r-1)-10*(10^r'-1) = 9,
```

equivalently `10^r=10^(r'+1)`. Hence `r=r'+1`, giving C. The alternatives
in (3.11) are exhaustive, so S and C exhaust `a=0`. Together with (3.8)--
(3.10) and reversal, this proves the theorem. QED.

## 4. Exact coefficient of every `+/-9*10^K` character

For `1 <= s <= H-2`, put

```text
W_s = (H-s-1)*(H-s).                                    (4.1)
```

Let `c_K^+` and `c_K^-` denote respectively the coefficients of
`Z^(9*10^K)` and `Z^(-9*10^K)` in (2.8), for `K >= 0`. Theorem 3.1 and the
literal cutoff (2.7) give the following complete contribution table.

| Family | Number/channel pair | Base difference | Common `k` range | Resulting `K` range | Coefficient contribution |
|---|---:|---:|---:|---:|---:|
| S | `j=1,...,9` | `9` | `0 <= k <= N-2` | `0 <= K <= N-2` | `9*(H-1)^2` |
| C | `(1,s+1;10,s)` | `9` | `0 <= k <= N-s-2` | `0 <= K <= N-s-2` | `W_s` |
| `V_1` | `(1,s+1;1,s)` | `9*10^s` | `0 <= k <= N-s-2` | `s <= K <= N-2` | `W_s` |
| `V_10` | `(10,s+1;10,s)` | `9*10^(s+1)` | `0 <= k <= N-s-2` | `s+1 <= K <= N-1` | `W_s` |

The last endpoint `K=N-1` occurs only in `V_10`: its base valuation `s+1`
exactly compensates for the terminal common index `k=N-s-2`. It would be lost
by the tempting but incorrect assertion that every multiplier-nine family
ends at `K=N-2`.

For an integer `x`, define the truncated prefix

```text
S_H(x) = sum_(1 <= s <= H-2, s <= x) W_s,               (4.2)
```

with an empty sum equal to zero. Equivalently, if

```text
m_H(x) = min(H-2,max(0,x)),
F(u) = u*(u+1)*(u-1)/3,
```

then changing variables `j=H-s` gives the closed form

```text
S_H(x) = F(H-1)-F(H-m_H(x)-1).                          (4.3)
```

### Theorem 4.1 (all endpoint truncations)

For every integer `K >= 0`, reversal symmetry gives `c_K^+=c_K^-=c_K`, and

```text
c_K = 9*(H-1)^2 * 1_[0,N-2](K)
    + S_H(N-K-2) * 1_[0,N-3](K)
    + S_H(K)     * 1_[0,N-2](K)
    + S_H(K-1)   * 1_[2,N-1](K).                        (4.4)
```

Here `1_[a,b](K)` is one when `a <= K <= b` and zero otherwise. In
particular,

```text
c_K = 0 for every K >= N.                               (4.5)
```

### Proof

First, every contribution to a requested final character satisfies

```text
(q(h,r)-q(h',r'))*10^k = epsilon*9*10^K.                (4.5a)
```

Necessarily `k<=K`: if `k>K`, the left side would be divisible by
`10^(K+1)`, while the right side is not. Cancelling `10^k` therefore gives

```text
q(h,r)-q(h',r') = epsilon*9*10^(K-k),                   (4.5b)
```

with the nonnegative base exponent `a=K-k`. Theorem 3.1 consequently applies
to every tuple contributing to the final character, not merely to a selected
subset.

For S, the character exponent is `9*10^k`, so `K=k`; summing its nine equal
weights gives the first term of (4.4). For C, again `K=k`, while its cutoff
is `K <= N-s-2`, equivalently `s <= N-K-2`; summing over all admissible `s`
gives the second term. For `V_1`, `K=s+k`; nonnegativity of `k` says `s<=K`,
and its upper cutoff says `K<=N-2`, giving the third term. For `V_10`,
`K=s+1+k`; hence `s<=K-1` and `K<=N-1`, giving the fourth term. Theorem 3.1
proves that there is no fifth contribution. Reversal preserves `W_s` and the
common `k` range, proving `c_K^-=c_K^+`. This proves (4.4)--(4.5). QED.

Thus (4.4), rather than an interior-only pattern, is the coefficient of every
requested positive and negative character. For additional endpoint checks,
put

```text
T_H = S_H(H-2) = H*(H-1)*(H-2)/3.                       (4.6)
```

Then the low and terminal coefficients are

```text
c_0     = 9*(H-1)^2 + T_H,
c_1     = 9*(H-1)^2 + T_H + (H-1)*(H-2),
c_(N-2) = 9*(H-1)^2 + 2*T_H,
c_(N-1) = T_H,
c_N     = 0.                                             (4.7)
```

All formulas include the smallest scale `t=0`, where `(N,H)=(5,3)`.

## 5. Growing interior coefficient and coefficient-mass obstruction

The ceiling definition gives

```text
(H-1)^2 < N <= H^2.                                     (5.1)
```

Since `H>=3` and all quantities are integral,

```text
N >= (H-1)^2+1 >= 2*H-1.                                (5.2)
```

Therefore the integer interval

```text
I_t = {K : H-1 <= K <= N-H}                             (5.3)
```

is nonempty and has exactly

```text
|I_t| = N-2*H+2 >= (H-2)^2.                             (5.4)
```

For every `K` in this interval, all three prefix sums in (4.4) have reached
their full value `T_H`. Hence every positive and negative interior coefficient
is exactly

```text
c_K = 9*(H-1)^2 + 3*T_H
    = (H-1)*(H^2+7*H-9).                                (5.5)
```

This is strictly positive and grows cubically in `H`. The adjacent transition
values provide a direct truncation check:

```text
c_(H-2)   = c_(H-1)-2,
c_(H-1)   = c_(N-H) = (H-1)*(H^2+7*H-9),
c_(N-H+1) = c_(N-H)-2.                                  (5.6)
```

Indeed, the omitted last prefix term is
`W_(H-2)=(H-(H-2)-1)*(H-(H-2))=2`.

Define the positive and two-sided multiplier-nine interior coefficient masses
after grouping equal Laurent characters by

```text
M_t^+   = sum_(K in I_t) |c_K^+|,
M_t^+/- = sum_(K in I_t) (|c_K^+|+|c_K^-|).             (5.7)
```

Equations (5.4)--(5.5) give the exact masses

```text
M_t^+ = (N-2*H+2)*(H-1)*(H^2+7*H-9),
M_t^+/- = 2*(N-2*H+2)*(H-1)*(H^2+7*H-9),               (5.8)
```

and the explicit lower bounds

```text
M_t^+   >= (H-2)^2*(H-1)*H^2,
M_t^+/- >= 2*(H-2)^2*(H-1)*H^2.                         (5.9)
```

Here `H=H_t` tends to infinity with `t`. More specifically, the coefficient-
mass scale needed before the outer factor `N-1` in (2.5) would be
`O(H^2*N)`, whereas (5.1) and (5.9) imply

```text
M_t^+/(H^2*N) >= (H-2)^2*(H-1)/H^2,                    (5.10)
```

which tends to infinity. Thus the complete multiplier-nine fiber is neither
zero in the interior nor supported on a target-scale boundary. The nine S
terms and the C, `V_1`, and `V_10` terms all have positive formal
coefficients; reversal creates the distinct conjugate character rather than a
negative coefficient. Therefore no coefficientwise algebraic telescoping
inside the `+/-9*10^K` fibers can repair the post-Cauchy dispersion bound.

## 6. Exact negative conclusion

The finite classification and (4.4) refute only the proposed mechanism of
grouping identical multiplier-nine Laurent characters and expecting their
interior coefficients to cancel, or to telescope to target-scale boundary
mass. They do not show that

```text
P_t(e(pi)), E_t(pi), Re A_t(pi), or |A_t(pi)|
```

is large. Upon evaluation, different Laurent characters
`e(+/-9*10^K*pi)` and characters outside the multiplier-nine sector can still
cancel. The Cauchy step (2.5) can also lose the one-sided sign information
needed by `(FP)`. Consequently this note supplies no evidence against `(FP)`,
T69's aggregate premise, the full T29 predicate, C3, C2, C1, or the canonical
ordered long-lag collision conjecture. Any proof of `(FP)` must use
cancellation between distinct Laurent characters or another fixed-`pi`
mechanism; this note does not decide whether such cancellation exists.
