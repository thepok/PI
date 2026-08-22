# Common T125 centered recurrence

For canonical BBP data at `N>=2`, use

```text
q_N=10^N-16
M_N=16^N*Lambda_N
S_N=sum_(j=0)^N nu_j*16^(N-j)*(Lambda_N/D_j)
h_N=gcd(Lambda_N,D_(N+1))
g_N=D_(N+1)/h_N=Lambda_(N+1)/Lambda_N
u_(N+1)=nu_(N+1)*Lambda_N/h_N
q_N*S_N=w_N*M_N+R_N
R_N=center_(M_N)(q_N*S_N) in [-M_N/2,M_N/2)
```

The exact updates are

```text
S_(N+1)=16*g_N*S_N+u_(N+1)
M_(N+1)=16*g_N*M_N
q_(N+1)=10*q_N+144
E_N=160*g_N*R_N+2304*g_N*S_N+q_(N+1)*u_(N+1)
E_N=k_N*M_(N+1)+R_(N+1)
k_N=w_(N+1)-10*w_N.
```

Equivalently, with `d_N=gcd(q_N,M_N)`, every local same-fiber replacement at
depth `N` is

```text
S_N(t)=S_N+t*M_N/d_N,
w_N(t)=w_N+t*q_N/d_N                         (t integer),
```

with `q_N,M_N,R_N,g_N,u_(N+1)` fixed and `S_N(t)>0`.  Extend it compatibly by
`S_(N+1)(t)=16*g_N*S_N(t)+u_(N+1)` and recompute the unique half-open
`R_(N+1)(t),w_(N+1)(t)`.  Such a replacement is noncanonical: it may refute an
inference based only on the displayed recurrence, but never refutes additional
canonical numerator structure.

Every `center` uses the half-open representative.  An outer state means

```text
R_N/M_N in [-1/2,-1/4] union [1/4,1/2).
```

The global T125 `conjecture` is that
`||(10^N-16)*pi||<1/4` for infinitely many `N`.  The rational shadow differs
from the real phase by less than
`eps_N=(5/8)^N/(15*(N+1)^2)`.  Proving the recurrence, shadowing, or a finite
table alone is not progress.

A rational central hit transfers to the real target only with the strict margin

```text
|R_N|/M_N < 1/4-eps_N.
```

The fold index has the exact definition
`k_N=floor(E_N/M_(N+1)+1/2)` and the safe canonical range
`427<=k_N<=582` for `N>=2` (derive any sharper range before using it).  For
branch analysis, put `r_N=R_N/M_N`, `f_N=(2304*g_N*S_N+q_(N+1)*u_(N+1))/M_(N+1)`;
branch `j` is the half-open set on which
`j=floor(10*r_N+f_N+1/2)`.  Do not assume all ten full-circle branches remain
nonempty after restricting `r_N` to the two outer quarters.

For the assigned probe, declare exactly one outcome:

- **GO:** the requested exact canonical exclusion/contradiction on an explicit
  unbounded depth class, including nonzero, divisibility, size, and endpoint
  proofs as applicable; or
- **STOP:** an exact counterexample or algebraic classification closing the
  precisely named mechanism on every depth class allowed by its quantifiers,
  with its same-fiber sensitivity boundary; or
- **OPEN:** neither GO nor STOP is established.  State the first exact missing
  implication.  OPEN is not promoted as a result.

Do not claim a STOP from a generic or noncanonical model unless the assigned
probe explicitly asks for a compatible full-composite replacement.  Do not
claim T125, `(D)`, or V1 from an algebraic identity.
