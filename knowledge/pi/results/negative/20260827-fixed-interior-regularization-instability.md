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

## Conditional translation-monodromy boundary

A separate audited `proof sketch` gives a narrow warning for finite local
systems.  Let `Q=10q`, `x_n={10^n*alpha}`,
`c_(Q,A+dq)=(A+dq+1/2)/Q`, and put

```text
J_n=floor(Q*x_n),      u_n=x_(n+k+1)-1/2.
```

Then exactly

```text
Q*(x_n-c_(Q,A+dq)) = J_n-A-dq+u_n.
```

If `Phi(t+m)=M^m Phi(t)` and a digit statistic is a linear aggregation of
`ell(Phi(Q*(x_n-c_(Q,A+dq))))` with digit-independent weights, it factors as

```text
S_d = ell(M^(-q*d) W).
```

At the next parent scale it becomes child-blind **only under the additional
uniform observable-periodicity condition** `ell*M^(-Q)=ell` on every
admissible next state (in particular if `M^Q=I` on the minimal observable
quotient).  Cylinder semantics alone does not imply this condition.  Indeed,

```text
M = diag(exp(2*pi*i/Q), exp(2*pi*i/(10*Q)))
```

can use its first eigenspace at scale `q` and its second at scale `Q`, retaining
a nontrivial decimal character at both levels.  Thus no broad one-step
Floquet, theta, Picard--Fuchs, or period-system collapse is claimed.  The
durable statement is only the exact factorization and the explicitly
conditional child-blindness result.

There is also a corrected pointwise T185 identity.  The machine-checked kernel
has

```text
Re boundaryMinorant_Q(t)
  = (cos(2*pi*t)-cos(pi/Q))
    * (sin^2(pi*Q*t)/(Q*sin^2(pi*t)))^2.
```

On an irrational decimal orbit,

```text
sin^2(pi*Q*(x_n-c_(Q,A+dq))) = cos^2(pi*x_(n+k+1)),
```

so the scaled sine numerator loses `A,d`, and the pointwise sign of the whole
kernel is exactly membership in the literal open target cylinder.  This
closes only attempts to obtain fresh target orientation from the numerator's
sign; magnitude-based aggregate inequalities remain open.  An earlier Pro
memo inverted the displayed quotient and overgeneralized the monodromy scope;
those claims are rejected.

## Provenance

Independently audited mathematical memo, completed 2026-08-27 UTC. Raw model
transcripts are intentionally not retained in the knowledge tree.
