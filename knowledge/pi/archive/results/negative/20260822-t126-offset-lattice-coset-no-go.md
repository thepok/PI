# T126: offset-lattice cosets do not select the canonical block return

Status: `proof sketch`

## Setup

Fix a depth `N >= 2` and block length `L >= 1`. Write

```text
M = M_N,
B = 16^L Lambda_(N+L)/Lambda_N,
M* = BM,
h = gcd(10^L,M).
```

The exact endpoint transport has the normalized form

```text
R* = center_(BM)(10^L B R + F),
```

where `F = C B S + q_end U` is the actual offset. No smallness of `F` is assumed. In particular, this note does **not** use the false bound `q_end U/M* < eps_N`; the registered tail bound involves the base coefficient `q_N`.

## Outer-quarter coset lemma

For every integer offset `F`, the map

```text
Phi_F(R) = center_(BM)(10^L B R + F)
```

maps each of the two old integer outer quarters onto the complete coset

```text
F + B h Z  (mod BM).
```

Indeed, write `10^L = h k` and `M = h m`, so `gcd(k,m)=1`. The image of `R mod M` under multiplication by `10^L B` is exactly `B h Z mod BM`. A prescribed point `F+Bhz` has preimages

```text
R = k^(-1) z  (mod m),       m=M/h.
```

Because `10 | M` and `L >= 1`, one has `h >= 10`. In the canonical centered convention the two integer sets are

```text
I_- = [-M/2,-M/4] intersect Z,
I_+ = [ M/4, M/2) intersect Z.
```

They contain respectively `M/4+1` and `M/4` consecutive integers. Since `m=M/h <= M/10 < M/4`, each contains at least `m` consecutive integers and hence a representative of every residue class modulo `m`. The endpoint `-M/2` and both quarter boundaries are included exactly as displayed; `M/2` is excluded.

Thus even after the input is restricted to either outer quarter, the offset lattice loses no point of its target coset.

## Clean `L=1` consequence

For `L=1`, `h=gcd(10,M)=10`. Since `M >= 256` and
`eps_(N+1) <= eps_3 = 125/122880 < 1/512`, the strict central interval

```text
(-BM(1/4-eps_(N+1)), BM(1/4-eps_(N+1)))
```

has length

```text
BM(1/2-2eps_(N+1)) > 127BM/256 >= 127B > 10B.
```

The two centered-complement components are

```text
[-BM/2, -BM(1/4-eps_(N+1))]
[ BM(1/4-eps_(N+1)), BM/2),
```

and each has length `BM(1/4+eps_(N+1)) > BM/4 >= 64B > 10B`. An open interval—or either displayed half-open/closed component—of length strictly greater than the coset spacing `10B` contains a coset point. Hence every target coset contains both a strict central point and an outer point, and each has a preimage in either chosen old outer quarter.

Consequently, knowledge only of the offset congruence modulo

```text
gcd(10B,BM)=10B
```

can neither send every integer input in either outer quarter centrally under this fixed-offset affine map nor exclude all outer outputs of that affine-domain test.

## Scope

This closes only an offset-lattice mechanism that treats the actual offset `F` through its coset. It does not constrain the single canonical residue `R_N`, does not discard the exact numerator or coefficient structure inside `F`, and does not close nonlinear or higher-depth selectors. It supplies no T125 return and no result on V1.

The source Oxzen memos were rejected because they used an unsupported endpoint-tail bound, incorrect gcd/valuation formulas, and invalid orbit-covering criteria. The statement above is the independently repaired residue-class consequence.

V1 remains open.
