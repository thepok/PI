# T141: the adjacent phase conductor is the full complementary lift modulus

Status: `proof sketch`
Last audited: 2026-08-22

## Exact conductor identity

Use the P16 notation at a base `n` and physical checkpoint `m`:

```text
T_m = B_(n,m) T_n,
R_(n,m) = B_(n,m) R_n,
H_n = T_n/R_n = T_m/R_(n,m).
```

For one selected phase put `Q_s=(10^(J_m+s)-16)/48`.  The compatible
entries are `e=c+R_(n,m) ell (mod T_m)`, with `ell mod H_n`.  Their phase
increment is therefore `Q_s ell/H_n (mod 1)`.  Its exact minimal period is

```text
h_s = H_n/gcd(H_n,Q_s).
```

This agrees with the P16 definition

```text
D_s=T_m/gcd(Q_s,T_m),
h_s=D_s/gcd(D_s,R_(n,m));
```

the equality follows prime-valuation by prime-valuation.

For the adjacent indices write `Q_-=Q_(-1)` and `Q_0=Q_(0)`.  Since all
relevant decimal indices are at least four,

```text
Q_0 = 10 Q_- + 3,
Q_- = 1 (mod 3),
gcd(Q_-,Q_0)=1.
```

Thus `gcd(H_n,Q_-)` and `gcd(H_n,Q_0)` are coprime divisors of `H_n`, and

```text
h_pair = lcm(h_-,h_0) = H_n.                         (1)
```

Equation (1) is independent of the canonical residue and of the BAD/HIT
arcs.  Enumerating the proposed adjacent-pair color period is exactly
enumerating every complementary lift `ell mod H_n`; it gives no conductor
compression.  In particular the fixed `h_pair<=4096` gate can run only when
the full complementary lift space itself has at most 4096 elements.

Also, `H_n>1` holds throughout the proposed range for a simple exact reason:
`D_1` contains `3^3`, division by `48` removes only one factor of `3`, and
`R_n` contains the full 2-part plus private primes `p>3`, but no factor of 3.
Hence `9|H_n` for every `n>=1`.

## Exact finite census

Status: `experiment`

The reproducer checks every base `10<=n<=64` and every physical checkpoint
`n<=m<=n+L_n`, using exact horizons and exact inclusive BBP denominators.  It
confirms (1) everywhere and finds no single-phase exception `h_s=1` (equivalently
`H_n|Q_s`).  The endpoint diagnostics are:

```text
n=10: H_n has 39 bits; minimum h_s = 40542838875 (36 bits)
n=64: H_n has 225 bits; minimum h_s has 205 bits.
```

At `n=10`, for example,

```text
H_10 = 527056905375
     = 3^4 5^3 7^2 11 13 17 19 23.
```

Reproducer:
[`workflows/research/pi/t141_phase_conductor_no_compression.py`](../../../../workflows/research/pi/t141_phase_conductor_no_compression.py)

Audited script SHA-256:

```text
b6025674e7de739fe52e257e61b85de4207d526685e3c1dfb105e476cfc54e11
```

## Scope

This is a scoped no-go for the P16 strategy of replacing the complementary
lift coordinate by the adjacent pair conductor and then enumerating its
colors.  It does not prove that OR-HIT coverage is impossible; a symbolic
argument over the full `H_n` colors could still exist.  It does not establish
an unbounded-family analytic obstruction, determine canonical HIT/BAD status,
or imply `(D)` or `V1`.

V1 remains open.
