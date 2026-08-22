# T151: bounded P22 affine divisor-switch review

Status: `experiment`  
Last audited: 2026-08-22

## Endpoint

The four-form affine divisor-switch target `ADS_(7/4)` remains `OPEN/HOLD`.
No sampled memo proved a power saving for either the complete mixed block
`DR+RD` or the complete same-ray off-diagonal block `DD+RR`, and none supplied
an exact counterfamily to the target.

## Bounded review

The direction gate fixed a cap of eight substantive memos, with at least
three from each provider.  Route-positive work had to prove an explicit
`X^(2-eta)` bound for one complete symmetry block using coefficient-specific
control of the switched equations

```text
u*q*A_s-v*q'*A_r=b*q*q'.
```

Correctly rewriting these equations, generic divisor bounds, fixed-pair
estimates, finite sparsity, or an unproved named sieve did not qualify.

All eight substantive memos were rejected:

| provider/run | memo SHA-256 | principal fatal gap |
|---|---|---|
| `ox-2` | `76861412e8743b37eca0f30ea8a40619d51a4c6d5e3451fb08d5e929bc7b23fa` | equations only; wrong parity and growth base |
| `oxzen-7` | `a544d8f12b2dbe4749c31eb0726c19a6ef31541ccb8dc949978a55684ed189fa` | invalid quotient/divisor ranges and no block power saving |
| `oxzen-6` | `9f8d0e8a4c73d5d5ecca0bcf0273ba3fe06f493ac222d645994614aea664c5de` | false central factorization invalidates the claimed cascade |
| `oxzen-10` | `91d498e143235e4d0f55349136820a216b26b555d116ff83adae9001777b92d8` | reversed reflected range and sign-invalid normal form |
| `oxzen-4` | `abc2a7eb6e47cb2f0c4886fdd4d998c9d5980b14236d3d98dca7d93af69f83e7` | no power saving and claimed census artifacts absent |
| `ox-5` | `1f9631add26cacf9ae2423e861dbe3330664f91a074f4008e24c55c024cbf31e` | false asymptotic and unsupported automatic zero-density claims |
| `ox-4` | `a37bfda64498e33dfe94348193c45fe767f2712cbfa389fa7451afc79778040e` | only `O(X^3 log X)` and incorrect RR congruence |
| `oxzen-12` | `495a70b8fd5e7b50a9d77ef47e081622dde12df832f044794f36488726155bd7` | wrong parity and a cumulative, truncated non-dyadic census |

The last memo correctly proved a Lucas--Frobenius digit-product congruence for
the coefficient sequence.  It gives no P22 gain because every actual record
already has the one-digit range `r<p`.  It is therefore not promoted as a
successor.

## Scope and final Gauss gate

This bounded failure is not a theorem that affine divisor switching cannot
work.  It shows that repeating the current weak-model task would be an
operational rabbit hole.  The off-diagonal remains open, while T150 leaves
the diagonal fixed-rho energy lemma open.

One final hard-creative Pro call is authorized on the more canonical
fixed-rho aggregate transfer-content certificate.  If it yields neither a
rigorous sublinear energy theorem nor an infinite structural obstruction,
the entire T143 Gauss second-moment branch moves to research HOLD.  No weaker
P23/P24 Gauss task or additional identical free-model wave follows without
genuinely new external mathematics.

No off-diagonal, diagonal, full-energy, `(D)`, or V1 result is claimed.

V1 remains open.
