# T142: the retained 2-primary character has dense BBP support

Status: `proof sketch`
Last audited: 2026-08-22

## Universal obstruction

Fix any P17 checkpoint `m` and selected phase with decimal index `j>=5`.
Write

```text
Q=(10^j-16)/48,
Dchar=T_m/gcd(Q,T_m).
```

Since `10^j=64 (mod 96)` for every `j>=5`, `Q` is odd.  Every `D_k` is odd,
so `Lambda_m` is odd and

```text
v_2(T_m)=v_2(16^m Lambda_m/48)=4m-4.
```

The odd coefficient `Q` removes none of this component.  Therefore `Dchar`
retains the full prime power `2^(4m-4)`.

For the registered BBP summand

```text
t_(m,k)=nu_k 16^(m-k) Lambda_m/D_k
```

the quotient `Lambda_m/D_k` is odd, hence

```text
v_2(t_(m,k))=v_2(nu_k)+4(m-k).
```

It is active modulo `2^(4m-4)` exactly when

```text
v_2(nu_k)<4k-4.                                      (1)
```

The exceptional indices are exact:

```text
k=0: nu_0=47,   inactive;
k=1: nu_1=318,  v_2(nu_1)=1, inactive;
k=2: nu_2=829,  v_2(nu_2)=0<4, active;
k=3: nu_3=1580, v_2(nu_3)=2<8, active.
```

For every `k>=4`, the stronger magnitude bound proves (1).  Its base is
`nu_4=2571<4096=2^12`, and

```text
nu_(k+1)=120k^2+391k+318,
16nu_k-nu_(k+1)=1800k^2+2025k+434>0.
```

Induction gives `nu_k<2^(4k-4)`, hence
`v_2(nu_k)<4k-4`, for all `k>=4`.

Thus the 2-primary active set is exactly `{2,...,m}`.  In particular the
full-composite union `U` contains every one of those indices, so

```text
|U|/(m+1) >= (m-1)/(m+1) -> 1.                      (2)
```

The centering contribution is not absent either:

```text
v_2(191 M_m/64)=4m-6<4m-4,
```

so it is nonzero modulo the retained 2-primary component.

Reproducer:
[`workflows/research/pi/t142_two_primary_dense_support.py`](../../../../workflows/research/pi/t142_two_primary_dense_support.py)

Audited script SHA-256:

```text
4878e60aa1c24b50f86b18b64a6315d93dd9993b993777336694b8d6ee8f6369
```

## Consequence and scope

Equation (2) universally rules out the P17 GO mechanism based on a bounded or
`O(log m)` full-composite active support.  Describing the dense interval as a
single “ray” while still summing all of its terms is precisely the rejected
`O(m)` rewrite, not compression.

This does not rule out a genuinely new algebraic closed form for the dense
sum, nor every possible single-character compression.  It proves no HIT/BAD
character, canonical return, `(D)`, or `V1` result.  It closes only the stated
P17 sparse-support GO class; odd-primary conductor savings cannot remove this
2-primary obstruction.

V1 remains open.
