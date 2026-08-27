# Linear scalar horizon-mask synthesis needs linearly many channels

Date: 2026-08-27 UTC

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

Source memo:
`workflows/state/chatgpt-pro/20260827-boundary-scale-survivor-i/answer.md`.
