# Common T126 canonical block arithmetic

For `N>=2`, `L>=1`, define

```text
q0=q_N=10^N-16                 q_end=q_(N+L)=10^L*q0+C
M=M_N=16^N*Lambda_N            G=Lambda_(N+L)/Lambda_N
B=16^L*G                       M*=M_(N+L)=B*M
C=16*(10^L-1)
S=S_N                          S*=S_(N+L)=B*S+U
w=w_N                          w*=w_(N+L)=10^L*w+K
q0*S=w*M+R                     R in [-M/2,M/2)
q_end*S*=w* M*+R*              R* in [-M*/2,M*/2)
```

Here `U=U_(N,L)` is the actual accumulated selected BBP fresh numerator, not a
free parameter.  The exact block equation, which is input rather than a result,
is

```text
K*M*+R* = 10^L*B*R + C*B*S + q_end*U.
```

The endpoint determinant is

```text
Delta=q0*K-C*w=q0*w*-q_end*w
Delta*M* = q_end*(B*R+q0*U)-q0*R*.
```

Audited baseline: the full rank-one integer module obtained by eliminating
`S` from only the two endpoint centering equations is already closed as a
small-versus-divisible route, including its primitive gcd normalization.  Do
not count rediscovering that determinant, its divisibility, or its size lower
bound as progress.  A new auxiliary must retain prefix-sensitive information,
use intermediate data, be nonlinear in a specified natural class, or otherwise
escape that exact row-elimination module.

Also `U/M*=A_(N+L)-A_N>0`, and the already-audited BBP shadow bound gives

```text
q0*(U/M*) < q0*(pi-A_N) < eps_N,
eps_N=(5/8)^N/(15*(N+1)^2).
```

An outer endpoint means `R/M in [-1/2,-1/4] union [1/4,1/2)` (and similarly
for `R*`).  A rational hit transfers to the real target only with
`|R_t|/M_t < 1/4-eps_t`; bare `<1/4` is insufficient.

For local same-fiber sensitivity put `d=gcd(q0,M)` and

```text
S(t)=S+t*M/d,     w(t)=w+t*q0/d,    t integer, S(t)>0.
```

Propagating the fixed actual fresh block gives `S*(t)=S*+t*M*/d`.  The endpoint
remainder is preserved exactly when `d | t*q_end`; all intermediate remainders
are preserved exactly when `d | t*q_(N+i)` for every `0<=i<=L`.  Such
replacements are noncanonical and may close only mechanisms explicitly shown
to depend on no further selected-numerator structure.

The memo must prove every divisibility, nonvanishing, strict size bound,
quantifier, and half-open endpoint it uses.  It must explain whether its
certificate changes under the displayed replacement.  Do not claim T125,
`(D)`, or V1 from an identity.  V1 remains open.
