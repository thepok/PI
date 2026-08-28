# Scalar horizon masks and exact state-only coboundaries fail

Date: 2026-08-27 UTC; scalar-coboundary extension audited 2026-08-28 UTC

Claim label: `proof sketch` (independently audited). This is a narrow method
separator, not progress on the missing fixed-pi sign estimate and not a claim
about arbitrary nonlinear decoders.

Let `q=10^k`, `k>=3`, and give every complete primitive-ray mode
`m=u*10^j` the horizon mask

```text
H_N(m) = 1  if j<N,
         0  if j>=N.
```

Suppose a pointwise linear Abel synthesis

```text
g(m) = sum_(ell=1)^J c_ell r_ell^m,   0<r_ell<1,
```

approximates this mask with `|g(m)-H_N(m)|<1/2` on the complete primitive
carrier. After merging repeated radii, necessarily

```text
J >= q/10.
```

Indeed, put `K=10^(N-1)` and take the `q/20` odd integers
`q/10<u<q/5`. The ordered, disjoint triples

```text
(10u-1)K,  10uK=u*10^N,  (10u+1)K
```

have mask values `1,0,1`: the outside modes have primitive bases `10u+-1`
at level `N-1`, while the middle mode has primitive base `u` at level `N`.
Thus `Re g(x)-1/2` has at least two real zeros per triple. It is a real
exponential polynomial with at most `J+1` distinct exponents (including the
constant exponent zero), so the Chebyshev/Rolle bound gives at most `J`
zeros. Hence `J>=2(q/20)=q/10`. The same proof applies to a linear heat
synthesis `sum c_ell exp(-tau_ell*m^2)` after setting `y=m^2`.

These are genuine modes rather than formal zero coefficients. For every
selected odd `u`, the primitive coefficient fibres are exactly

```text
fiber(10u+-1) = {10u+-1},   fiber(u) = {u,10u}.
```

The singleton coefficients are nonzero. Cancellation in the two-point fibre
would require

```text
9u(2A+1) = q  (mod 2q),
```

which is impossible because the left side is odd and `q` is even. On the
subfamily `q/10<u<3q/20`, containing `q/40` odd integers, the coefficient
formula moreover gives

```text
|primitiveRayCoefficient(q,A,u)| >= sqrt(7/20)/q^2.
```

The scope is important. This only obstructs **linear pointwise multiplier
synthesis of the sharp horizon mask** by scalar Abel/heat channels. It does
not prove that `q/10` scalar observations are necessary for a nonlinear
decoder, nor for recovering just one fixed target-weighted aggregate:
coefficient cancellations could avoid pointwise mask reconstruction. The
singular Mahler cocycle in the source memo remains an exact repackaging of the
open sign and is not promoted as a new bridge lemma.

## Complete T189 drift is not an exact scalar `L2` coboundary

A separate audited Fourier-ray argument rules out another scalar mechanism.
Let `q>=1000`, `A` be a target label, and `d<10`.  Expand the actual complete
T189 fresh drift per orbit point, including the zero sector, all nine nonzero
sectors, the factor `q`, and the constant T176 potential penalty, as the real
trigonometric polynomial `W_(q,A,d)`.  Then there are no `F in L2(R/Z)` and
`C in R` with

```text
W_(q,A,d)(x) = F(10*x mod 1) - F(x) + C       almost everywhere.
```

The decisive frequency is `u=20*q-1`.  It occurs uniquely in the nonzero
sector at `ell=2*q-1`, `r=9`.  Its positive-frequency coefficient in `W` is

```text
5*q*positiveBoundaryCoefficient(10*q,20*q-1)*unitPhase,
```

which is nonzero: T142's endpoint formula gives
`positiveBoundaryCoefficient(Q,2*Q-1)=1/(2*Q^2)` for `Q=10*q`.  Primitive
compression puts every zero-sector frequency at most `2*q-1`, and the
potential penalty is constant, so neither can cancel this top coefficient.
There are no frequencies `10^j*u` for `j>=1`.

For `T(x)=10*x mod 1`, Fourier coefficients of a putative coboundary obey,
for nonzero `m`,

```text
W_hat(m) = (if 10 divides m then F_hat(m/10) else 0) - F_hat(m).
```

Since `10` does not divide `u`, the nonzero coefficient at `u` and the zero
coefficients at every `10^j*u` force
`F_hat(10^j*u)=-W_hat(u)` for all `j>=0`.  This contradicts Fourier-coefficient
decay for `F in L2`.

This corrected proof is stronger than the initially proposed argument, whose
claim that the zero sector lived in residue class `0 mod 10` was false after
primitive compression.  The result rules out only an **exact scalar
state-only equality**.  It gives no sign for pi and does not rule out
digit/vector state, inequalities, approximate coboundaries, or finite-horizon
pi-specific mechanisms.  It is a narrow method separator, not progress on
FMR.

There is also an `L1` strengthening for the finite **nonzero-sector** block
alone (`proof sketch`).  Its one-step real carrier has a nonzero frequency-1
coefficient and only frequencies prime to 10.  Over horizons `N <= n < H`,
the coefficient on the ray `10^j` is therefore a fixed nonzero `c` exactly
for `N <= j < H`.  If the block were `u-u∘T+r` with `u,r in L1` and `r`
globally nonnegative or globally nonpositive, zero Haar mean would force
`r=0`; the Fourier recurrence would then force
`u_hat(10^j)=(H-N)c` for every `j>=H`, contradicting Riemann--Lebesgue.
This excludes only exact scalar `L1` decompositions with a globally one-signed
remainder.  It does not exclude approximate, vector/cone, or pointwise-pi
transport.  Decimal-periodic rationals merely intersect both open sign
regions; neither sign class is claimed dense in the whole circle.

The result combines two independently audited mathematical memos. The later
scalar-coboundary argument corrected the earlier zero-sector support claim;
the incorrect argument and raw model transcripts are not retained.
