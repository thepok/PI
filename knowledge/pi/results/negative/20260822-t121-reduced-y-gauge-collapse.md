# T121 reduced-`y` gauge collapse

Date: 2026-08-22 UTC

Status: `proof sketch`

This note uses a different rational state from the canonical T121 note.  Keep
`A_N` for the BBP partial sum, put `m_N=10^N-16`, and reduce

```text
y_N=m_N*A_N=Ptilde_N/Qtilde_N.
```

For the finite-window argument fix `2<=N<L`, so every `m_j` in the window is
positive.  Let `atilde_N=floor(Ptilde_N/Qtilde_N+1/2)` and
`Deltatilde_N=Ptilde_N-atilde_N*Qtilde_N`, using the frozen centered half-tie
convention.  If the next BBP increment is the reduced rational `u_(N+1)/v_(N+1)`
and `ell_N=m_(N+1)`, then an unreduced successor vector is obtained from

```text
M_N = [[ell_N*v_(N+1), ell_N*m_N*u_(N+1)],
       [0,               m_N*v_(N+1)       ]].
```

For the shear `T(a)=[[1,a],[0,1]]`, the centered one-step matrix is

```text
C_N=T(-atilde_(N+1))*M_N*T(atilde_N).
```

Therefore every finite product telescopes exactly:

```text
C_(L-1)*...*C_N
  =T(-atilde_L)*M_(L-1)*...*M_N*T(atilde_N).
```

Primitive gcd normalization does not change this projective identity.  More
precisely, for a nonsingular integer matrix `C` and nonzero integer vector `w`,

```text
prim(C*prim(w))=prim(C*w).
```

Thus all intermediate nearest-integer shears cancel, and all intermediate gcd
reductions can be postponed to the endpoint.  Projectively unrolling the
remaining upper-triangular matrices gives only

```text
Deltatilde_L/Qtilde_L
 = (m_L/m_N)*(Deltatilde_N/Qtilde_N)
   +m_L*(A_L-A_N)+(m_L/m_N)*atilde_N-atilde_L
 = m_L*A_L-atilde_L.
```

The last equality is the definition of the endpoint centered value, not a
descent estimate.  Likewise, for nonzero `Deltatilde_L`, the complete rational
product formula reads

```text
(|Deltatilde_L|/Qtilde_L)
 * product_p |Deltatilde_L/Qtilde_L|_p = 1,
```

whose finite-place factor is tautologically `Qtilde_L/|Deltatilde_L|`; it is
not an independent Archimedean bound.

## Exact scope

This closes only endpoint arguments based on multiplying the reduced-`y`
centered matrices, primitive gcd normalization, or evaluating the complete
rational product formula.  It is not the canonical T121 recurrence for reduced
`A_N=P_N/Q_N`, and it does not rule out BBP-specific use of those canonical
gcds or cross-index coefficient correlations.  It also discards every
intermediate centered inequality, so it does not close the T122 carry-language
question about pathwise admissibility of actual carry blocks.  No return,
`(D)`, or V1 follows; V1 remains open.

The result was proposed by an authenticated ChatGPT 5.6 Pro research turn and
then independently checked for algebra, notation, novelty, and claim scope by
two reviewers.  The broader Pro memo was not retained because its coboundary
calculation duplicated existing knowledge and its linear-form bound was only a
restatement of the target.
