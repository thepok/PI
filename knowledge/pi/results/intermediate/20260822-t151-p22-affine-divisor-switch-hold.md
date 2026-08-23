# T151: bounded P22 affine divisor-switch review

Status: `experiment`  
Last audited: 2026-08-23

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

The authorized final hard-creative Pro call on the more canonical fixed-rho
aggregate transfer-content certificate has now completed and been audited.
Its retained source provenance is:

```text
model: ChatGPT 5.4 Pro
conversation: https://chatgpt.com/c/6a8a1f0b-1f20-83eb-a058-2a9a14ecd645
local source: workflows/state/chatgpt-pro/runs/fixed-i-aggregate-energy-20260822/answer.md
answer SHA-256: 20a2dc18ec55fff16857e8b68aec3e485178fd9b11471487d42b8c78b898f6c2
check manifest: ok true, status done; browser closed; no downloads
```

### Retained result

Status: `proof sketch`

Let $r_h$ be the number of pairs of fixed-sequence zeros at difference
$h$, and let $b_n$ be the registered self-convolution.  The Pro derivation
was independently audited for the following exact fixed-gap content.
After clearing the Legendre transfer recurrence, its start-index polynomial
$Q_h(X)$ satisfies, with $\varepsilon_h=(h-1)\bmod2$,

\[
 Q_h(-X-h-1)=(-1)^{h-1}Q_h(X),
 \qquad
 Q_h(X)=Y^{\varepsilon_h}\Phi_h(Y^2),
 \quad Y=2X+h+1,
\]

where

\[
 \deg\Phi_h\le\left\lfloor{h-1\over2}\right\rfloor,
 \qquad
 \operatorname{lc}(\Phi_h)=2^{-2(h-1)}b_{h-1}.
\]

Actual starts give distinct roots of $\Phi_h$.  Therefore

\[
 b_{h-1}\not\equiv0\pmod p
 \quad\Longrightarrow\quad
 r_h\le\left\lfloor{h-1\over2}\right\rfloor.
\]

Consequently, for every odd prime $p>503$ and

\[
 3\le H\le
 \left\lfloor{2p\over5}\right\rfloor-
 \left\lceil{p\over11}\right\rceil,
\]

define the short-lag energy

\[
 E_p(\le H)=\sum_{h\le H}(r_h-1)_+,
\]

Then

\[
 b_1,\ldots,b_{H-1}\not\equiv0\pmod p
 \quad\Longrightarrow\quad
 E_p(\le H)\le\left\lfloor{(H-3)^2\over4}\right\rfloor.
\]

Under the frozen short-convolution hypothesis this gives the genuine but
limited estimate

\[
 E_p(\le D_p)<{1\over4}p^{2/3}.
\]

For

\[
 F_p(X)=\prod_{z\in Z_p}(X-z),
 \qquad
 \mathcal R_p(Y)=Y^{-|Z_p|}
 \operatorname{Res}_X(F_p(X),F_p(X+Y)),
\]

the interval width is less than $p/2$, and the full multiplicities have the
exact resultant encoding

\[
 \deg\gcd(\mathcal R_p,\mathcal R_p')=2E_p.
\]

These identities were independently replayed for small $h$, including the
dyadic coefficients of $\Phi_h\in\mathbb Z[1/2][U]$, and their interval,
denominator, split/inert, and multiplicity conditions were audited.

### Gate verdict

The displayed block-diagonal determinant is only a product of independent
fixed-$h$ interpolation determinants.  It contains no cross-$h$ coupling;
the short-lag estimate merely sums the separate degree bounds.  In
particular, it gives no control of

\[
 E_p^{>D_p}=\sum_{h>D_p}(r_h-1)_+.
\]

The first missing line remains a sublinear bound for this long-lag energy.
The Pro answer supplied neither that bound nor an infinite obstruction or
counterfamily for the actual fixed sequence.  Its arithmetic-progression
example only proves that the complete collection of separate fixed-gap
degree bounds is structurally insufficient.

Operational state: **research HOLD**.  P21, `ADS_(7/4)`, and the complete
T143 diagonal/off-diagonal second-moment branch remain mathematically
`OPEN`; HOLD is a prioritization decision, not `Outcome: STOP` and not a
theorem that aggregate transfer or affine divisor switching cannot work.
Resume only after genuinely new external mathematics addressing fixed-i
cross-gap compatibility, actual four-form correlations, or an exact
fixed-sequence obstruction.  No weaker P23/P24 Gauss task or additional
identical free-model wave follows.

No off-diagonal, diagonal, full-energy, `(D)`, or V1 result is claimed.

V1 remains open.
