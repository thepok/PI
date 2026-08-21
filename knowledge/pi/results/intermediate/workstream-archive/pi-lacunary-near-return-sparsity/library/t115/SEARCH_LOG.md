# T115 bounded search log

Date: 2026-08-10 UTC.

The search was stopped after four primary papers.  No paper was added merely to
fill the source cap, and only one system survived the duplicate and quantifier
filters.

| Lane | Query or lead | Opened primary source | Decision |
|---|---|---|---|
| symbolic entropy/collision and substitution spectra | `generalised Thue Morse autocorrelation recursion Riesz product` | Baake--Gahler--Grimm, arXiv:1201.1423v1 | retain `(k,l)=(5,5)` because length ten gives an exact finite decimal-ray recursion |
| fixed-point lacunary spectral dynamics | `bijective substitution spectral cocycle Riesz product Lyapunov 2024` | Marshall-Maldonado, arXiv:2210.11982v2 | screen: exact product but only almost-everywhere pointwise asymptotics; no pi or growing-prefix uniformity |
| fixed-point diffraction comparator | `period doubling autocorrelation exact recursion diffraction` | Baake--Grimm, arXiv:1007.0707v1 | screen: pure point, named-system overlap with T91, and no needed new finite decimal mechanism |
| symbolic/fractal Fourier comparator | `Thue Morse finite Riesz product coefficient recursion` | Baake--Grimm, arXiv:0809.0580v1 | screen: radix two leaves residual frequency `h*5^r`; distinct Gowers route already compared in T110 |

## Candidate accounting

```text
inspected primary sources: 4
retained candidates: 1
candidate: generalized Thue--Morse substitution rho_(5,5)
```

## Exclusion filters applied

- Invariant-measure separator: the limiting generalized Thue--Morse measure is
  not used for a Birkhoff/generic-point transfer.  Only finite densities and
  their exact coefficient recursion are retained.
- Paperfolding recurrence: excluded through T91/T94/T97/T101 comparison.
- Toeplitz tower: excluded through T103 comparison.
- Ambient Fourier decay: excluded through T104 comparison.
- Gowers or nilsequence mechanism: excluded through T110 comparison.
- Finite carry cocycle: excluded through T112 comparison.
- Variable-threshold avoidance: no row-dependent threshold or selected
  after-the-fact cutoff is used; the spike holds for every `r` at `N=r+1`.
- Determinant nonvanishing: no determinant argument occurs.

## Stop reason

The first retained base-ten system already has the exact finite obstruction
`c_(r+1)(10^r)=7/10`.  Further candidate collection could not improve the
cheapest rejection test and risked duplicating the existing automatic,
ambient-measure, or carry-cocycle portfolios.  The scout therefore stopped at
four sources and one candidate.
