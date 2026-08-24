# Exact current PI interface (2026-08-24)

For the decimal pi orbit `x_n=fract(10^n*pi)`, the active alternatives are:

1. A wordwise target-centered signed Jackson defect `D(q,N,a)`. An empty
   interval `[a,a+1/q)` forces `D>=c_q`, where
   `c_q=1/(3q)+2/(3q^3)`. Thus for each nonempty word `s`, any `N_s>0` with
   `D(10^|s|,N_s,a_s)<c_q` forces a hit and the full wordwise premise implies
   V1. Frequency aggregation and directional-before-modulus are already done;
   fixed-pi smallness is open.
2. Moving-mesh uniform integrability (UI) on selected consecutive blocks:
   with counts `n_j(a)`, lengths `L_j`, and cell counts `q_j`, require
   `lim_(M->inf) sup_j (1/L_j) sum_(a:n_j(a)>M L_j/q_j)n_j(a)=0`.
   Exact times-ten dynamics plus `L_j,q_j->inf` and UI imply selected-block
   Haar limits and V1. Collision and bounded relative entropy are stronger
   sufficient premises. No fixed-pi UI estimate is known.

New audited no-go: `alpha=sum_(j>=1)10^(-A_j)`, `A_j=j*2^j`, satisfies
`IrrationalityMeasureBelow(alpha,B)` for every `B>3` and exact
`EffectiveIrrationality(alpha,4,1,10^64)`, but every moving-mesh selection
fails UI. If `q/L` is unbounded, every occupied cell eventually exceeds the
tail threshold; if bounded, all but `O((log L)^2)` block points lie in the
first cell. Therefore effective irrationality, periodic-window exclusion,
digit-change counts, and fixed-frequency gaps alone cannot yield UI/collision.
Any advance must add a genuinely pi-specific aggregate-lag,
numerator-sensitive, or phase-sensitive mechanism.

Exact identities available: `S_(10h)(N)=S_h(N)-e(h*x_0)+e(h*x_N)`; aggregated
Jackson coefficients are positive on `|h|<=2q-1`, have zero mode `c_q`, total
mass `2`, and support endpoint coefficient `A_q(2q-1)=1/(2q^2)`.

Nothing here proves fixed-pi cancellation, UI, V1, density, or normality.
