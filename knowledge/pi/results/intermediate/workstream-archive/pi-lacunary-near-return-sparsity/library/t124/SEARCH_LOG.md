# T124 bounded search log

Search date: 2026-08-10 UTC.

The search cap was twelve primary sources. It stopped after eight. Exactly
three systems were retained. Searches were organized by mechanism rather than
by desired conclusion, and every inspected source appears below.

| ID | Lane and bounded query | Exact primary source inspected | Decision |
|---|---|---|---|
| S1 | Hypergeometric/G-function: `integral hypergeometric monodromy arithmetic companion matrices congruence` | Singh--Venkataramana, arXiv:1208.6460v2 | Retain H1 and H2. It supplies exact operators, companion matrices, and arithmeticity. |
| S2 | Arithmetic monodromy: `perfect Zariski closure congruence quotient expansion squarefree` | Salehi Golsefidy--Varju, arXiv:1108.4900v3 | Use for H2 theorem-domain test. It stops at squarefree moduli. |
| S3 | Arithmetic Fourier/expansion: `SL_d modulo q arbitrary expander prime powers` | Bourgain--Varju, arXiv:1006.3365 | Use for H1. It covers every positive modulus but requires Zariski density in `SL_d`. |
| S4 | Short structured sums: `composite modulus subgroup incomplete exponential sum prime powers` | Bourgain--Chang, GAFA 16 (2006) | Screen out. The fixed factor-count and prime-order hypotheses fail on `10^m`. |
| S5 | Mahler/functional recursion: `Rudin Shapiro polynomial recurrence uniform Fourier bound` | Erdelyi, arXiv:1406.2233 | Retain M1. Exact square-root Fourier bound; exact decimal specialization freezes. |
| S6 | Symbolic Fourier/collision: `Thue Morse Riesz recursion autocorrelation` | Baake--Grimm, arXiv:0809.0580 | Screen out as an already represented binary substitution fingerprint. |
| S7 | Symbolic entropy/uniformity: `automatic sequence Gowers Rudin Shapiro Thue Morse` | Konieczny, arXiv:1611.09985v2 | Calibration only. Fixed-order signed uniformity does not control the required unweighted lacunary phase. |
| S8 | Fractal Fourier decay: `analytic self conformal measure polynomial Fourier decay nonlinearity` | Baker--Banaji, arXiv:2401.01241v2 | Screen out. Decimal branches are affine, and an ambient measure would not select a deterministic fiber. |

## Candidate retention ledger

| Candidate | Recurrence present | Integral congruence action present | Growing decimal theorem | Displayed calculation | Cheap test |
|---|---:|---:|---:|---:|---:|
| H1 rank-two Gauss hypergeometric | yes | yes, exactly `SL_2(Z/10^m Z)` | yes, for branching words | (H1.4)--(H1.6) | deterministic coding absent |
| H2 rank-four symplectic hypergeometric | yes | yes | no in inspected source | (H2.5)--(H2.6) | S2 is squarefree-only; deterministic coding still absent |
| M1 Rudin--Shapiro Mahler cocycle | yes | deterministic semigroup state | no | (M1.8)--(M1.10) | orbit freezes in `O(log m)` |

No fourth candidate was retained. Thue--Morse would duplicate T115/T121's
substitution/automatic fingerprint, while S4 and S8 are analytic tools rather
than exact recurrence systems satisfying the candidate specification.

## Availability audit

The supplied library contained readable reports for every mandated comparator
through T121 except rejected T119, whose content-addressed prior report was
recoverable elsewhere in the supplied record. No readable T122 or T123
artifact was present. Their active leases were treated as availability facts
only.

No novelty claim beyond this bounded corpus is made.
