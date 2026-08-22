# T120 S2 literal-four-pole verifier guidance

Status: planned and inactive. The future verifier owns a literal four-pole
route physically separated from S1. It may see only a controller job and an
immutable CAS copy after S1 exits. It cannot mint receipts or run window 13.
Use verifier-owned normalized signed numerator/positive-denominator arithmetic
with gcd reduction. `fractions.Fraction` and the S1 combined numerator identity
are forbidden. Reconstruct literal four-pole endpoint partials and obtain the
forcing term from their exact difference.
The forcing is exactly `F_N = 10^(N+1) * (P_(N+1) - P_N)`; an unscaled
endpoint difference is invalid.
It must independently recompute the complete parent/S0 256-point statistic,
maximum-ratio/tie, identity, and decision artifact rather than trust summaries.
