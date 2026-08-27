# Fixed-interior regularizations lose the fresh target branch exponentially

Claim label: `proof sketch`

## Result

Let `zeta = exp(2*pi*i/10)` and, for a target digit `t`, put

```text
Q_t(y) = Re sum_(m=1)^9 zeta^(-m t) exp(2*pi*i*m*y).
```

At decimal grid points, `Q_t(t/10)=9` and `Q_t(s/10)=-1` for `s != t`.
Also `||Q_t'||_infty <= 90*pi`.

Fix `N>=0`, `H>=1`, `n=N+H-1`, and `K=10^n`. Choose a neighbouring digit
`s != t`, so `|s-t|=1`, and for any `0<=a<K` define

```text
x_t = (a+t/10)/K,   x_s = (a+s/10)/K.
```

These numbers share their first `n` decimal digits and differ at the fresh
digit. For

```text
S_(t;N,H)(x) = sum_(q=N)^n Q_t(10^q*x),
```

the newest term has exact signed gap `10`. The derivative bound controls all
earlier terms, giving

```text
S_(t;N,H)(x_t) - S_(t;N,H)(x_s)
  >= 10 - pi*(1-10^(1-H)) > 10-pi.                 (1)
```

Now consider any finite vector of complete target-weighted regularizations

```text
A_j(x) = sum_(q=N)^infinity sum_(m=1)^9
           zeta^(-m t) lambda_(j,m,q) exp(2*pi*i*m*10^q*x)
```

whose first spectral moments

```text
M_j = sum_(q,m) m*10^q*|lambda_(j,m,q)|
```

are finite, and put `M=(sum_j M_j^2)^(1/2)`. Direct phase Lipschitz control
then gives the whole-future estimate

```text
||A(x_t)-A(x_s)||_2 <= pi*M/(5*10^n).              (2)
```

If an `L_n`-Lipschitz decoder recovers both fresh signed sums within error
`epsilon < G_H/2`, where `G_H` is the right side of (1), (1)--(2) force

```text
L_n >= 5*10^n*(G_H-2*epsilon)/(pi*M).              (3)
```

Thus a fixed finite collection of interior Abel/Mahler/Poisson values, or
positive-time heat/theta values, cannot feed a horizon-uniform stable signed
consumer. Although those transforms contain the entire infinite future, they
are exponentially insensitive to the newest target branch.

## Audit

The operator independently checked the root-of-unity gap, the derivative
constant, the geometric sum in (1), and the termwise complex-exponential
bound in (2). The result is retained as a `proof sketch`, not as
`machine-checked`: the general regularization statement and its special
Abel/heat corollaries have not been formalized in Lean.

This is narrower and stronger than the finite-cylinder separator. It rules
out stable extraction from a complete infinite transformed sum whenever its
first spectral moment stays bounded independently of the fresh horizon.

## Surviving route

The argument does not exclude singular boundary-scale sampling. A transform
route must now do at least one of the following:

- take `1-r = O(10^-n)` for Abel/Mahler sampling;
- take heat time `tau = O(10^(-2n))`;
- control an exponentially ill-conditioned decoder; or
- provide a genuinely discontinuous pi-specific arithmetic invariant.

The next creative target is therefore a one-sided arithmetic theorem for the
target-weighted transform at the decimal boundary scale, not another fixed
interior positivity or analyticity statement.

## Source

Independently audited ChatGPT Pro memo from
`workflows/state/chatgpt-pro/20260827-alternate-signed-tail-h/answer.md`,
completed 2026-08-27 UTC.
