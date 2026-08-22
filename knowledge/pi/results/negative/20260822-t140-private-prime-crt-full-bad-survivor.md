# T140: a private-prime CRT class contains a full-BAD cylinder survivor

Status: `experiment`
Last audited: 2026-08-22

## Result

The proposed private-prime CRT full BAD cylinder does **not** eliminate its
canonical CRT residue class at the first tested horizon `n=10`.  Exact integer
arithmetic gives

```text
L_10 = 3
P_10 = 13840197668021
T_10 = 501279153857749830020441598590976000
r_10 = 13814527577135
t_0  = 12294962618106739655891
x_0  = r_10 + P_10 t_0
     = 170164712955526266975539796722538846.
```

The entry `x_0` lies in `[0,T_10)`, has the independently reconstructed
canonical residue `r_10 mod P_10`, and is literal BAD in both selected phases
at every physical checkpoint `m=10,11,12,13`.  It is not asserted to be the
canonical entry `e_10`.

The private prime-power data `(p,k_p,a,e mod p^a)` are

```text
(29,3,1,6), (31,7,1,2), (37,4,1,31), (41,5,1,12),
(43,10,1,8), (53,6,1,28), (61,7,1,57), (73,9,1,27).
```

Each residue is derived from the unique surviving summand

```text
nu_(k_p) 16^(10-k_p) (Lambda_10/D_(k_p)) mod p^a,
```

not by reading `e_10`.  Only after CRT assembly does the verifier check the
consistency `e_10 = r_10 (mod P_10)`.

## Exact propagation and stability

Status: `proof sketch`

For `10<=m<=13`, direct separation of the inclusive BBP sum proves

```text
S_m = (M_m/M_10) S_10 + V_(10,m),
V_(10,m) = sum_(k=11..m) nu_k 16^(m-k) Lambda_m/D_k.
```

Thus a candidate entry propagates without canonical-state substitution as

```text
E_m(x) = ((T_m/T_10)x + V_(10,m)) mod T_m.
```

At each of the eight selected phases, let `mu_(m,s)>0` be the exact circular
distance of its centered value from the adjacent boundary of the good arc
`(-1/4+eps_j,1/4-eps_j)`.  Replacing the CRT lift parameter `t` by `t+h`
changes that phase on the circle by

```text
q_j h / (48 H),        H=T_10/P_10.
```

Consequently every phase stays BAD whenever

```text
|h| <= rho H,          rho=min_(m,s) 48 mu_(m,s)/q_j.
```

The exact verifier obtains `floor(rho H)=2893`; hence all `5787` consecutive
lifts `t_0-2893,...,t_0+2893` survive the complete four-checkpoint cylinder.
It also replays each lift directly.  The tight constraint is `(m,s)=(13,0)`,
and the next lower lift fails it.

Reproducer:
[`workflows/research/pi/t140_private_prime_crt_survivor.py`](../../../../workflows/research/pi/t140_private_prime_crt_survivor.py)

Audited script SHA-256:

```text
f51ce7915449598246b1e0978d3edc8467d4ce0de3ec071174e594571f7aea47
```

## Scope

This is a finite, noncanonical-survivor obstruction to using the private-prime
congruence alone as a separator.  It does not prove survivors for an unbounded
family, does not determine the actual canonical entry's BAD status, and does
not rule out augmenting the CRT data with genuinely independent information.
It is not a solution, a canonical return theorem, progress on `(D)`, or
progress on `V1`.

V1 remains open.
