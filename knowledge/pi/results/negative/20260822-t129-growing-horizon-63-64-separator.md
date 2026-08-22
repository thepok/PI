# T129: the `63/64` local separator persists to a growing horizon

Date: 2026-08-22 UTC

Status: `proof sketch`

This note retains the independently repaired mathematics from the T129 free
provider portfolio.  The two P1 construction memos have SHA-256 values
`4e6dec9bc169475635caae10108ed6b04f4614c0e3ce9b75f1258760650cc44c`
(OpenRouter) and
`c2cc9dcdebdcc9af7fc8bc388cd882035be5ccfa4dbedcfc073d948f221ffb0e`
(Oxzen).  The focused P2 envelope memo has SHA-256
`ec9242db9e4fdf4b59a560175c8d2b4163b5886ac2f75f5c7332771adb1fc46f`.
None is retained verbatim: independent audits repaired their centering,
denominator, endpoint-factor, and strict-rounding errors.

## Registered data

Use

```text
nu_j=120j^2+151j+47,
D_j=(2j+1)(4j+3)(8j+1)(8j+5),
Lambda_j=lcm(D_0,...,D_j),
M_j=16^j*Lambda_j,
S_j=sum_(h<=j) nu_h*16^(j-h)*(Lambda_j/D_h),
A_j=S_j/M_j,
q_j=10^j-16.
```

For `N>=6` and `i>=0`, put

```text
B_(N,i)=M_(N+i)/M_N,
U_(N,i)=S_(N+i)-B_(N,i)S_N
       =M_(N+i)(A_(N+i)-A_N).
```

Then `B_(N,i)` and `U_(N,i)` are integers, `U_(N,0)=0`, and
`U_(N,i)>0` for `i>0`.  If

```text
a_j=M_(j+1)/M_j,
u_(j+1)=S_(j+1)-a_j*S_j
```

is the actual fresh numerator, direct subtraction gives

```text
U_(N,i+1)=a_(N+i)U_(N,i)+u_(N+i+1).          (1)
```

Thus the block offsets propagate through every actual one-step numerator, not
merely through an endpoint identity.

## Improved positive tail

The exact polynomial expansion is

```text
D_k=512k^4+1024k^3+712k^2+194k+15,

5D_k-8k^2*nu_k
 =1600k^4+3912k^3+3184k^2+970k+75 > 0.
```

Consequently `nu_k/D_k<5/(8k^2)` for `k>=1`.  Summing the actual
`16^(-k)` BBP tail, rather than a surrogate series, gives

```text
0 < pi-A_N
  = sum_(k>=N+1) 16^(-k)*nu_k/D_k
  < [5/(8(N+1)^2)] * sum_(k>=N+1)16^(-k)
  = 16^(-N)/(24(N+1)^2).                     (2)
```

This improves the previously registered constant `1/15` to `1/24`.

## Exact integral window

At each depth `j=N+i`, define

```text
S~_j=63M_j/64+U_(N,i),
w~_j=63*10^j/64-16,
R~_j=M_j/4+q_j*U_(N,i).                       (3)
```

These are integers because `64|M_j` and `64|10^j` for `j>=6`; moreover
`S~_j>0`.  The base identity

```text
q_j*(63M_j/64)
 =(63*10^j/64-16)M_j+M_j/4
```

and (1) prove, respectively,

```text
q_j*S~_j=w~_j*M_j+R~_j,
S~_(j+1)=a_j*S~_j+u_(j+1).                    (4)
```

No congruence involving `S~_j` itself is needed.

For `0<=i<=L`, positivity of the BBP terms and (2) give

```text
0 <= q_(N+i)*U_(N,i)/M_(N+i)
   = q_(N+i)(A_(N+i)-A_N)
   < 10^(N+i)*16^(-N)/(24(N+1)^2)
   = 10^i*(5/8)^N/(24(N+1)^2).                (5)
```

Equality on the left occurs only at `i=0`.

Therefore, if

```text
10^L*(5/8)^N <= 6(N+1)^2,                    (H)
```

then the strict upper estimate in (5) yields

```text
M_(N+i)/4 <= R~_(N+i) < M_(N+i)/2
```

for every `0<=i<=L`.  These are exactly the unique representatives in the
half-open centered intervals `[-M_(N+i)/2,M_(N+i)/2)`.  At `i=0`, including
the one-point window `L=0`, the residue is exactly `M_N/4`.

Every residue in the constructed window is therefore outside the strict T125
sufficient region

```text
|R_j|/M_j < 1/4-eps_j.
```

## Critical growing horizon

Let

```text
alpha=log_10(8/5).
```

Condition (H) is equivalent to

```text
L <= E_24(N)
     := alpha*N+2log_10(N+1)+log_10(6).       (6)
```

For an integer `L`, (6) is exactly

```text
L <= floor(E_24(N)).
```

In fact `E_24(N)` is never an integer.  Otherwise

```text
10^E_24 = 6(N+1)^2(8/5)^N
```

would be an integral power of `10`; after reduction the right side retains a
factor `3` in its numerator while its denominator contains only powers of
`5`.  Hence one may equivalently write

```text
L <= ceil(E_24(N))-1.                          (7)
```

Consequences include:

- every fixed `L` is covered for all sufficiently large `N`;
- every integer `L<=alpha*N` is covered for every `N>=6`;
- the critical slope `alpha=0.204119982...` itself is covered, with an
  additional `2log_10(N+1)+log_10(6)` horizon allowance.

The word critical here refers to this separator estimate, not to a proved
threshold for canonical residues.

## First-term lower bound and transition band

The same construction has a nearly matching necessary bound for its raw
positive-quarter formula.  Let `L>=1`, `m=N+L`, `k=N+1`, and

```text
X=10^L*(5/8)^N,
delta_(N,L)=q_m(A_m-A_N).
```

The first omitted positive BBP term gives

```text
delta_(N,L) >= q_m*16^(-(N+1))*nu_(N+1)/D_(N+1).  (8)
```

For `k>=7`, the rational function `k^2*nu_k/D_k` is increasing and

```text
k^2*nu_k/D_k >= 38024/179645.
```

One direct check expands the numerator of the forward difference as

```text
4770+77097k+328475k^2+615308k^3
 +572808k^4+259456k^5+45568k^6 > 0.
```

Also `m>=7` gives

```text
q_m/10^m >= 624999/625000.
```

Combining these facts with
`10^m*16^(-(N+1))=X/16` yields the audited two-sided estimate

```text
[2970620247/224556250000] * X/(N+1)^2
 <= delta_(N,L)
 < X/[24(N+1)^2].                              (9)
```

Put

```text
K=56139062500/2970620247=18.8980946173...
```

Then

```text
X <= 6(N+1)^2       => delta_(N,L)<1/4,
X >= K(N+1)^2       => delta_(N,L)>=1/4.       (10)
```

The second condition means that the raw expression in (3) reaches or exceeds
`M_m/2` and no longer lies in the claimed half-open positive outer quarter.
It does not determine the centered residue after wrapping.

The safe and forced-wrap real envelopes differ by only

```text
log_10(K/6)=0.4982667687... < 1.
```

Thus at each fixed `N>=6`, at most one integer block length lies between the
certified no-wrap and certified-wrap ranges.  This is a two-sided threshold
for this construction only, not a digit-return theorem.

## Local-separator scope

Fix `N,L` satisfying (H), and consider all integral windows with the actual
fixed coefficients and fresh numerators, satisfying the numerator recurrences
and centered equations.  The state (3) belongs to this class and has no strict
hit.  Therefore the bare local hypotheses—and any additional identity that is
true for every state in this class—cannot imply that every such window
contains a strict hit.

This conclusion does not apply to an arbitrary added premise: a premise may
exclude (3).  In particular the exact selected canonical numerator `S_N`, its
finite-sum provenance, global prefix consistency before `N`, canonical
quotient data, or a canonical-only sign/divisor/selector property remain valid
escape routes.

The theorem extends T128's three-depth firewall to a linearly growing horizon,
but it says nothing about the actual canonical residues and gives no T125,
`(D)`, or V1 progress.

V1 remains open.
