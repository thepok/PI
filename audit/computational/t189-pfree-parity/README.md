# T189 p-free preferred-parity separator

Claim label: the mathematical reduction is a `proof sketch`; the finite
outward-interval leaves are an `experiment`.  This is not a Lean theorem or a
machine-checked claim.

The replay tests the certified positive seed `(q,A,N)=(1000,334,1000)` and
all seven literal FMR children.  It finds the exact root witness set
`{0,1,2,3,4,8,9}` and, at every reached `q=10000` node, both complete
inherited-deficit-corrected parity averages strictly negative.  The worst
upper bound is

```text
max(M_even,M_odd) < -8424.30118897787522947.
```

Thus a p-free Machin carrier within digitwise transfer buffers `E_D,E_G`
cannot satisfy the preferred-parity premise
`max(M_even°,M_odd°)>E_D+E_G` at the next step: clipping is
one-Lipschitz, so the carrier maximum is `<E_D+E_G-8424`.  This closes only
that parity-average route from this seed.  It does not close literal FMR,
full multi-sector transport, other seeds, T189, or V1.  At `(10000,1334)`,
literal FMR still holds uniquely at `d=5`.

## Reproduce

```bash
OMP_NUM_THREADS=5 ./audit/computational/t189-pfree-parity/reproduce.sh
```

Requirements: GCC with OpenMP, GMP development headers, Python 3, binary
floating point, and at least a 64-bit `long double` mantissa.  On the audited
x86 binary80 machine, the interval portion took about 36 seconds with five
threads and roughly 7.6 MB maximum RSS per 100,000-point node.

`pi_cert.cpp` constructs an exact rational Chudnovsky bracket and fixes
`floor(10^100050*pi)`.  The standard Chudnovsky identity itself is an external
mathematical input, not proved in this bundle.  `t189_interval_cert.cpp`
implements the exact T174 spatial identity, signed zero coefficient, T139
endpoint correction, T178 surplus normalization, and outward interval
arithmetic.  Parity means use interval division by exact five; no binary
`0.2` constant is trusted.

The expected summary is architecture-sensitive at its last printed digits.
The strict margins are many orders of magnitude larger than interval widths;
a differing platform should audit signs rather than silently replacing the
tracked baseline.
