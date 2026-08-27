# T133 recurrence-weighted address collapse

Status: `proof sketch`

A full run of bad T130 pair states forces failure at every consecutive decimal
depth covered by the run.  However, the natural base-10 recurrence-weighted
aggregate of the individual BBP increments telescopes exactly to endpoint
data.  Thus that specific restricted-denominator/address aggregate cannot
provide the missing intermediate canonical obstruction.

V1 remains open.

## Consecutive-depth cover

Let the pair state be bad at every base

```text
m=n,n+1,...,n+L.
```

The pair at `m` consists of the sufficient-hit tests at

```text
{J_m-1,J_m}.
```

Since the audited step law is

```text
J_(m+1)-J_m in {1,2},
```

successive two-point sets have no integer gap.  Hence every sufficient hit
`G_k` fails throughout the inclusive consecutive interval

```text
J_n-1 <= k <= J_(n+L).                            (1)
```

For `L=0`, (1) is exactly the initial pair.

## Selected decimal recurrence

Put

```text
b_(k+1)=A_(k+1)-A_k,
Y_k=q_k A_k,
C_k=144A_k+q_(k+1)b_(k+1).
```

Because `q_(k+1)=10q_k+144`,

```text
Y_(k+1)=10Y_k+C_k.                               (2)
```

Choose the half-open centered remainder and its nearest integer by

```text
z_k=floor(Y_k+1/2),
y_k=Y_k-z_k in [-1/2,1/2),
c_k=z_(k+1)-10z_k in Z.
```

Then (2) gives the exact selected carry recurrence

```text
y_(k+1)=10y_k+C_k-c_k.                           (3)
```

Under (1), each `y_k` lies in the exact closed bad exterior

```text
[-1/2,-(1/4-eps_k)] union [1/4-eps_k,1/2).
```

Thus the full run is representable as a variable-length half-open carry
cylinder retaining every prefix constraint.

## Endpoint telescoping

Iterating (2) yields, for every `h>=1`,

```text
sum_(r=0..h-1) 10^(h-1-r) C_(K+r)
=Y_(K+h)-10^h Y_K.                               (4)
```

The corresponding geometrically weighted carry sum from (3) likewise
reduces to the two centered endpoints.  Therefore any proposed
restricted-denominator condition which uses the individual forcing terms
only through the recurrence-compatible weighted sum in (4) is endpoint-only.
Cross-multiplication cannot recover the discarded prefix information.

## Scope

This is a scoped negative result for the obvious base-10 Duhamel/address
aggregate, not a general linear variable-length no-go.  Arbitrary coefficient
weights, the full vector of `C_k`, individual increments, all prefix
inequalities, selected carry signs, nonlinear functions, congruences, and
canonical numerator restrictions may retain intermediate information.

In particular, (4) does not collapse the bad-run cylinder itself and proves
no eventual escape.  A viable continuation must derive an independent
coefficient-specific restriction on the selected canonical carry word, not
merely repackage (2)--(4).
