# T64: exact T29 scale audit and variable-phase fourth moment

Status: **proof sketch** for a variable-phase residual-A12 sibling.  The T29
and T63 interfaces cited below are machine-checked; the new metric argument in
this note is not Lean-formalized.  This note proves no estimate at the fixed
phase `Real.pi`, and proves neither C2 nor C1.

## 1. Statement pin, scope, and quantifiers

The byte-exact canonical statement is delivered as `CANONICAL_STATEMENT.txt`.
Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical statement is locally formulated and has no external source URL.
It asks about the fixed phase pi, all positive `m,N`, and ordered long-lag
collisions.  The result below is instead the following explicitly labeled
sibling:

* alpha is Lebesgue-random in `[0,1)`;
* only the residual-A12 primitive sector is tested;
* `m=1`, `L_t=2^t`, and `N_t=4 L_t+1`;
* the assertion is simultaneous in the countable family `t >= 0`, but it says
  nothing about other `m,N`;
* only pi inside the orbit phase is replaced: the Fourier convention retains
  the factor `2*pi`.

Thus every metric conclusion below is a **variable-phase sibling conclusion**.
There is no fourth-moment estimate here for pi, C2, or C1.

## 2. Machine-checked interfaces used

The accumulated library supplies these kernel-checked modules:

```text
TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
TheoryLib.PiLongLagBlockCollisionDecay.T63T63ExactFiniteFourthMoment
```

The exact imported interfaces relevant here are:

* `T29.WidthWeightedSquareFunctionAt`: at `m=1`, its right side is
  `10*A*(N + N^2*10^(-s))`, because the inclusive frequency set is exactly
  `Icc 1 10` and `decimalFrequency 1=10`.
* `T29.widthWeight`: for the literal block `[1,N_t)`, the width is
  `sqrt(N_t^2-1)`, not its length and not an asymptotic substitute.
* `T63.dyadic_one_block_audit`: `L_t=2^t`, `N_t=4*2^t+1`, and the translated
  canonical partition is the singleton block `[1,N_t)`.
* `T63.C_eq_fourthMoment`: for each literal `1 <= h <= 10`, the positive
  primitive representative sum is one half of the exact polynomial displayed
  in Section 3.
* `T63.complete_selected_defect_recombination`: selected and unmatched-defect
  representatives exhaust the primitive sector, and the factor `2` restores
  both signed orientations before division by the literal width.

T63 instantiates its characters at pi.  Section 4 gives a separate finite
algebra proof that the same polynomial identity holds after replacing only the
phase argument by alpha.  No fixed-pi asymptotic is imported or inferred.

## 3. Literal specialization and the exact fourth-moment frontier

Fix `t >= 0` and abbreviate

```text
L = 2^t,
N = N_t = 4*L+1,
W = W_t = sqrt(N^2-1),
T_s = T_s(1,N) = N + N^2*10^(-s).
```

For a phase beta, put

```text
T_h,beta(N) = sum_{0 <= k < N} exp(2*pi*i*h*10^k*beta),
X_h,beta(N) = |T_h,beta(N)|^2,
F_t(beta) = sum_{h=1}^{10} X_h,beta(N)^2,
S_t(beta) = sum_{h=1}^{10} X_h,beta(N).
```

All ten `X_h,beta(N)` are nonnegative.  T63's complete two-orientation
selected-plus-defect expression, with beta substituted only in the phases, is

```text
J_t(beta)
  = (1/W) * sum_{h=1}^{10}
      [X_h,beta(N)^2
       - 4*(N-1)*X_h,beta(N)
       + 2*N^2 - 3*N]
  = [F_t(beta) - 4*(N-1)*S_t(beta) + 20*N^2 - 30*N]/W.       (3.1)
```

This retains the literal width, the linear fourth-moment correction, and both
lower-order polynomial terms.  In particular, replacing (3.1) by `F_t/N`
would not be an exact audit.

T29's actual specialized full-square-function assertion is

```text
widthWeightedSquareFunction 8 1 Q0 1 N beta
  <= 10*A*(N + N^2*10^(-s)).
```

At this one-block scale its left side has the literal denominator `W`, but it
contains the complete square function, not just `J_t`.  To test whether the
primitive contribution is compatible with that scale, assign it the chosen
primitive-sector budget

```text
J_t(beta) <= 10*A*T_s.                                      (3.2)
```

Thus (3.2) uses T29's exact right-hand scale but is not itself a predicate
declared by T29.  Proving it does not bound the cancelling sector, diagonal
mean, or any other part of T29's full square function.

Let `K_N=20*N^2-30*N` and `R=10*A*W*T_s`.  The exact condition before reducing
to `F_t` alone is

```text
F_t - 4*(N-1)*S_t + K_N <= R.                               (3.3)
```

Since the ten `X_h` are nonnegative,

```text
sqrt(F_t) <= S_t <= sqrt(10*F_t).                            (3.4)
```

The left inequality follows by expanding `S_t^2`; the right one is
Cauchy-Schwarz.  Because the coefficient of `S_t` in (3.3) is negative, the
largest possible left side among all nonnegative ten-tuples having a fixed
value of `F_t` occurs at `S_t=sqrt(F_t)`.  Consequently the sharp sufficient
condition expressible from `F_t` alone is

```text
F_t - 4*(N-1)*sqrt(F_t) + 20*N^2 - 30*N
  <= 10*A*sqrt(N^2-1)*(N + N^2*10^(-s)).                    (3.5)
```

It is sharp at the level of arbitrary nonnegative ten-tuples because
`(X_1,...,X_10)=(sqrt(F_t),0,...,0)` has `S_t=sqrt(F_t)`.  This does not assert
that every such tuple comes from an orbit.

For readers wanting cancellation-free control, (3.4) also gives the stronger
absolute-value criterion

```text
F_t + 4*(N-1)*sqrt(10*F_t) + 20*N^2 - 30*N
  <= 10*A*sqrt(N^2-1)*(N + N^2*10^(-s)),                    (3.6)
```

which implies `|J_t(beta)| <= 10*A*T_s`.  Here `K_N>0` because `N>=5`.

The growth frontier is now explicit.  For `0<s<1` and `N>=5`,

```text
W = sqrt(N^2-1) >= N-1 >= (4/5)*N,
T_s >= N^2*10^(-s) >= N^2/10,
10*W*T_s >= (4/5)*N^3.                                     (3.7)
```

Also `K_N <= 20*N^2 <= 4*N^3`.  Therefore `F_t <= B*N^3`
implies (3.2), for every `0<s<1`, with the explicit choice

```text
A = (5/4)*(B+4).                                            (3.8)
```

For the stronger absolute target, (3.6) holds with

```text
A_abs = (5/4)*(B + 4*sqrt(10*B) + 4),                       (3.9)
```

because `4*(N-1)*sqrt(10*F_t) <= 4*sqrt(10*B)*N^3`.
Thus exponent three is the weakest upper-growth exponent supplied by an
`F_t`-only audit.  If only `F_t=O(N^beta)` is known with `beta>3`, the positive
`F_t` term can dominate the target; the negative correction is at most order
`N^(1+beta/2)`, which is lower order when `beta>2`.  No such growth hypothesis
alone then guarantees (3.2).

## 4. Phase-independent proof of the exact polynomial

This section verifies that (3.1) is valid for every real beta, rather than
silently extending T63's fixed-pi theorem.

Fix `h,N,beta` and write

```text
z_k = exp(2*pi*i*h*10^k*beta),
T = sum_{k<N} z_k,
X = |T|^2.
```

Every `|z_k|=1`.  The sum over ordered unequal pairs is

```text
Q = sum_{a,b<N; a!=b} z_a*conj(z_b) = X-N.                  (4.1)
```

Start with `Q*conj(Q)=(X-N)^2`.  The primitive/nonattacking domain excludes
the two attacks `a=c` and `b=d`.  For one attack, summing a row gives

```text
sum_{a<N} |T-z_a|^2
  = sum_a [X+1-2*Re(T*conj(z_a))]
  = N*X+N-2*X.                                              (4.2)
```

The second attack has the same value.  Their intersection consists of the
`N*(N-1)` ordered unequal pairs, each contributing one.  Inclusion-exclusion
therefore gives

```text
(X-N)^2 - 2*(N*X+N-2*X) + N*(N-1)
  = X^2 - 4*(N-1)*X + 2*N^2 - 3*N.                         (4.3)
```

This uses only `|z_k|=1`, so it holds for every beta.  The finite primitive
orientation pairing sends a positive difference `d` and its reverse to

```text
exp(2*pi*i*h*d*beta) + exp(-2*pi*i*h*d*beta)
  = 2*cos(2*pi*h*d*beta).
```

The selected and unmatched-defect sets are the exhaustive disjoint partition
used by T63.  Summing (4.3) over the literal frequencies `h=1,...,10` and
dividing by `W` proves (3.1) for the variable-phase sibling.

## 5. Exact additive-relation count and expectation

Now let alpha be uniformly distributed on `[0,1)`.  Expanding one fourth
moment and using the elementary character integral gives

```text
E[|T_h,alpha(N)|^4]
  = sum_{a,b,c,d<N}
      integral_0^1 exp(2*pi*i*h*(10^a-10^b+10^c-10^d)*alpha) d alpha
  = #{(a,b,c,d) in {0,...,N-1}^4 : 10^a+10^c=10^b+10^d}.   (5.1)
```

Indeed the frequency is an integer, and the integral is one at frequency zero
and zero otherwise.  The factor `h` is nonzero for every `1<=h<=10`, so it
does not change the zero-frequency condition.

We next count (5.1), without finite computation.  Sort each pair so that
`a<=c` and `b<=d`.  The largest power of 10 dividing `10^a+10^c` is exactly
`10^a`: after division by `10^a`, the remaining factor is either `2` (if
`a=c`) or `1+10^(c-a)` (if `a<c`), neither divisible by 10.  The same argument
on the right shows `a=b`.  Division by `10^a` then gives `10^(c-a)=10^(d-a)`,
so `c=d`.  Hence the original ordered pairs have the same multiset:

```text
10^a+10^c=10^b+10^d  iff  {a,c}={b,d} as multisets.         (5.2)
```

There are `N` choices with `a=c`, each allowing one ordered pair `(b,d)`.
There are `N^2-N` ordered choices with `a!=c`, each allowing the two orders
`(b,d)=(a,c)` and `(c,a)`.  Thus the exact relation count is

```text
N + 2*(N^2-N) = 2*N^2-N.                                   (5.3)
```

Equations (5.1)-(5.3) prove, for every `1<=h<=10`,

```text
E[|T_h,alpha(N)|^4] = 2*N^2-N.
```

Linearity of expectation does not require independence between the ten
frequencies.  Therefore, at `N=N_t`,

```text
E[F_t] = 10*(2*N_t^2-N_t).                                 (5.4)
```

## 6. Summable tails and the almost-sure envelope

For `t>=1`, define

```text
E_t = {alpha : F_t(alpha) > 10*(2*N_t^2-N_t)*t^2}.
```

Markov's inequality and (5.4) give the explicit tail

```text
Leb(E_t) <= E[F_t]/[10*(2*N_t^2-N_t)*t^2] = 1/t^2.          (6.1)
```

The tail is summable:

```text
sum_{t=1}^infinity Leb(E_t) <= sum_{t=1}^infinity 1/t^2 < infinity. (6.2)
```

For completeness, the first Borel-Cantelli conclusion here follows directly
from the union bound.  For every `M`,

```text
Leb(union_{t>=M} E_t) <= sum_{t>=M} Leb(E_t),
```

and the right side tends to zero.  Since `limsup E_t` is contained in every
such tail union, it has measure zero.  No independence assumption is used.

Consequently, for Lebesgue-almost every alpha one may choose
`t_0(alpha)>=1` such that for all `t>=t_0(alpha)`,

```text
F_t(alpha)
  <= 10*(2*N_t^2-N_t)*t^2
  <= 20*N_t^2*t^2.                                         (6.3)
```

This is the requested almost-sure envelope, with the explicit eventual
constant 20.  To include every `t>=0`, absorb the finitely many exceptions:

```text
C_alpha = max(20,
  max_{0<=t<t_0(alpha)} F_t(alpha)/[N_t^2*(t+1)^2]).
```

Then `C_alpha<infinity` and

```text
F_t(alpha) <= C_alpha*N_t^2*(t+1)^2  for every t>=0.        (6.4)
```

Equivalently, after changing the random constant, one has
`F_t(alpha)<=C'_alpha*N_t^2*t^2` for every `t>=1`.

## 7. Exact compatibility verdict

The elementary bound

```text
(t+1)^2 <= (9/4)*2^t                                      (7.1)
```

holds for every `t>=0`.  It is checked directly through `t=3`; from there the
ratio of consecutive squares is at most `25/16<2`, giving induction.  Since
`2^t=(N_t-1)/4<N_t/4`, (6.4) and (7.1) imply

```text
F_t(alpha) <= (9*C_alpha/16)*N_t^3.                        (7.2)
```

Put `B_alpha=9*C_alpha/16`.  Equations (3.7), (3.8), and (7.2) show that, for
almost every alpha, all `t>=0` and every `0<s<1`,

```text
J_t(alpha) <= 10*A_alpha*(N_t+N_t^2*10^(-s)),
A_alpha = (5/4)*(B_alpha+4).                               (7.3)
```

If an absolute-value sector estimate is preferred, (3.9) gives

```text
|J_t(alpha)| <= 10*A_abs,alpha*(N_t+N_t^2*10^(-s)),
A_abs,alpha = (5/4)*(B_alpha+4*sqrt(10*B_alpha)+4).         (7.4)
```

**Variable-phase sibling verdict:** the chosen complete-primitive budget at
T29's exact one-block right-hand scale has the fourth-moment growth frontier
`F_t=O(N_t^3)`.  The proved metric envelope is the strictly stronger

```text
F_t=O_alpha(N_t^2*t^2)=O_alpha(N_t^2*(log N_t)^2).
```

Thus there is no remaining exponent or logarithmic gap in this variable-phase
test.  There is a spare factor asymptotic to `N_t/t^2`.  This verdict concerns
only the complete selected-plus-defect primitive sector on the displayed
dyadic `m=1` family.  It supplies no fourth-moment estimate at pi, does not
establish T29's full all-block predicate C2, and does not establish C1.

## 8. Local integrity check

From a directory containing only the delivered artifacts, run

```sh
sha256sum -c SHA256SUMS
```

This checks both the byte-exact canonical statement and this note.
