# Full π stream: rational tail correction, not digit distribution

Status: **proof sketch**. Coordinator inspected the full derivation and separate
audits of the tail, denominators, and avoiding control. No Lean verification or
novelty claim. This is an actual-π approximation improvement, not a theorem
overcoming quiet-window dependence for π. A separate restricted construction
is recorded in the [square-digit-sum note](20260907-square-digitsum-tail-translations.md);
its mechanism has no established transfer to this π stream.

## Exact stream and correction

Let X=π/4, σ_e=(-1)^floor((e−1)/2), and

    u_e=σ_e/(2e−1)+1_{2|e}σ_e/(e−1),
    P_n=Σ_{e=1}^n u_e2^(-e), Y_n=2^nP_n, R_n=2^n(X−P_n).

The identity follows by grouping imaginary terms in −Log(1−(1+i)/2), as
in the [filtered-series note](20260907-filtered-pi-growing-cofactors.md),
but here no terms are omitted. Exactly Y_(n+1)=2Y_n+u_(n+1),
R_(n+1)=2R_n−u_(n+1), and Y_n+R_n=2^nX.

Define H(z)=∫_0^1 t^(z−1)/(4+t²) dt. Summing the four-periodic signs gives

    R_n=σ_(n+1)H(n+1/2)+(σ_(n+2)/2)H(n+3/2)
          + σ_(n+2)H(n+1)                    if n is even,

with the last summand replaced by 2σ_(n+1)H(n) if n is odd.
For the first stream, integrate the generating function
Σ_{j≥1}σ_(n+j)y^(j−1)=(σ_(n+1)+σ_(n+2)y)/(1+y²), then substitute t².
For the second, select even or odd j according to n. Absolute convergence
justifies the operations. In particular R_n=σ_(n+1)/(2n)+O(n^−2).

The endpoint expansion 1/(4+t²)=Σ_{j≥0}a_j(1−t)^j has

    a₀=1/5, a₁=2/25, 5a_j=2a_(j−1)−a_(j−2),
    |a_j|≤(1/2)5^(-(j+1)/2), 5^(j+1)a_j∈Z.

Replace H in the exact formula by the rational function

    H_K(z)=Σ_{j<K} a_j j!/[z(z+1)…(z+j)]

to define C_(n,K). No π digits are required to compute it. The geometric
series remainder and beta integral give, for n,K≥1,

    |R_n−C_(n,K)|≤2·5^(-K/2) K!/[n(n+1)…(n+K)].

Indeed the kernel remainder is at most
5^(-K/2)(1−t)^K/[2(√5−1)], and the sum of absolute coefficients in the
tail formula is at most 7/2; 7/[4(√5−1)]<2.

Set K=floor(n/4), C_n=C_(n,K), Z_n=Y_n+C_n, n≥4. Since
K!/[n…(n+K)]=(1/n)∏_{i=1}^K i/(n+i)≤4^(-K)/n,

    E_n:=|R_n−C_n|≤(8√5/n)2^(-n/2)5^(-n/8).

## Tracking and denominator costs

For n≥8 write den(Z_n)=2^b_n Q_n in lowest terms, Q_n odd, and
2^b_n Z_n=A_n/Q_n. Then

    b_n≤floor(log₂(n+K)),
    |2^(n+t)X−2^tZ_n|≤(8√5/n)5^(-n/8), 0≤t<floor(n/2).

Thus the usable rational orbit A_n2^j/Q_n tracks actual π shifts at
n+b_n+j for 0≤j<L_n=floor(n/2)−b_n=n/2−O(log n).
The full Fourier-sum transfer error at integer frequency h is at most
(16π√5 |h|/n)5^(-n/8), by summing the geometric errors 2^tE_n.
This is a transfer bound, not cancellation of either sum.

For the preperiod bound, expand (1−t)^j first: 5^K H_K(z) is an integer
linear combination of 1/(z+r), 0≤r<K. Its denominator therefore divides
an LCM, not a product. Half-integer arguments give odd denominators, even
after the displayed factor 1/2; integer arguments lie between n and n+K.
The largest possible denominator power of two is floor(log₂(n+K)).

Every prime q with n+K+1<q≤2n−1 survives with exact exponent v_q(Q_n)=1.
In Y_n its unique occurrence is the first-stream term e=(q+1)/2 with
coefficient a signed power of two divided by q. All other terms are
q-integral. C_n has coefficient denominator a power of 5, integer
denominators below q, and odd half-integer denominators strictly between
q and 2q. It is q-integral, so cannot cancel this valuation. Consequently

    ∏_{n+K+1<q≤2n−1, q prime} q ≤ Q_n
      and Q_n divides 5^K lcm{d≤2n+2K+1 : d odd}.

Using the prime number theorem, these elementary bounds imply
(3/4+o(1))n≤log Q_n≤(5/2+(log 5)/4+o(1))n. The exact prime-survival
claim itself does not use that asymptotic input. Hence the available
window has length Θ(log Q_n), below a complete period: ord_(Q_n)(2)
≥log₂(Q_n+1)>L_n eventually. Character-completion bounds on the
square-root-modulus scale give no saving here. A bound on the specific
numerator's short orbit has not been established.

## An avoiding control with exponentially close injections

Define q₀=1/3, q_n=σ_(n+1)/(2n+3) for 1≤n≤3, and q_n=C_n for n≥4.
Let d_e=2^(-e−1) when e=4^j, j≥1, and zero otherwise. The rational rule

    û_e=2q_(e−1)−q_e+d_e

has limit β=Σû_e2^(-e)=1/3+Σ_{j≥1}2^(-(2·4^j+1)), by telescoping.
Its binary expansion retains a one in every even position; additions
change distinct odd-position zeros to ones without carries. It avoids 00
and is irrational, since the modified odd positions have unbounded gaps.

With c=(log(4√5))/4<log 2, the correction estimate gives

    û_e−u_e=O(e^(-1)exp(−ce)),
    R̂_n−R_n=O(n^(-1)exp(−cn)).

Thus eventual signs and all algebraic tail asymptotics agree, but

    Σ_{t<N} exp(2πi·3·2^tβ)=N+O(log(N+2)).

To see the last bound, digit additions at positions ℓ_j≤t and the rational
baseline contribute integers at frequency 3. The remaining deviation is
at most 6πΣ_{ℓ_j>t}2^(t−ℓ_j). Summing over t costs less than one per
active ℓ_j plus a bounded remaining tail; there are O(log N) active positions.
This control does not satisfy the identical rational formula for u_e.
It defeats cancellation inferred only from signs, asymptotics, rationality,
or a small corrected recurrence defect, not every possible π-specific proof.

## Exact numerator certificate (proof sketch)

Retain n≥8 and the reduced A_n,Q_n,b_n above. Let S_n be the primes
n+K+1<q≤2n−1, D_n=∏_{q∈S_n}q, M_n=Q_n/D_n, and v_n=n+b_n−1.
For χ₄(q)=(-1)^((q−1)/2), the unique denominator-q term gives

    qZ_n ≡ σ_((q+1)/2)2^(n−(q+1)/2) ≡ χ₄(q)2^(n−1) (mod q),
    A_n(Q_n/q)^(-1) ≡ χ₄(q)2^v_n (mod q).

These are localized rational congruences: qZ_n, not Z_n, is q-integral.
For the second equality use σ_((q+1)/2)=(-2/q) and Euler's criterion
2^(-(q−1)/2)≡(2/q), where the parentheses denote Legendre symbols.
The factor 2^b_n is necessary when passing to the reduced numerator.

Set B_n=Σ_{q∈S_n}χ₄(q)D_n/q. Chinese remaindering gives the exact identity

    V_n=(A_n−2^v_n M_n B_n)/D_n ∈ Z,
    A_n/Q_n = 2^v_n B_n/D_n + V_n/M_n,
    gcd(B_n,D_n)=gcd(V_n,M_n)=1.

Indeed, modulo each q only its own summand in B_n survives. The local
congruence proves integrality of V_n. Reducing D_n V_n≡A_n modulo M_n
proves its coprimality, since gcd(D_n,M_n)=1 by exact prime survival.
Empty products and sums use D_n=1 and B_n=0.

This certificate distinguishes the avoiding control above: its corrected
value is exactly 2^n(1/3+Σ_{4^j≤n}2^(-(2·4^j+1))), with denominator
supported only on 2 and 3. Thus q Ẑ_n≡0 at every selected prime, unlike
qZ_n. This separation alone is not a sufficient digit hypothesis.

In particular the character sum is a synchronized product:

    Σ_{j<L_n} e(hA_n2^j/Q_n)
      = Σ_{j<L_n} e(hV_n2^j/M_n) ∏_{q∈S_n} e(hχ₄(q)2^(v_n+j)/q),
    e(t)=exp(2πit).

The cofactor and shared index cannot be discarded. Even cancellation of
each separate prime factor does not bound this product sum. No joint
saving or occurrence follows from the certificate. The symbolic argument
was checked independently and by the coordinator; it is not Lean-verified
and no novelty is claimed. Exact finite checks are not its infinite proof.

## Research disposition

The common-time moving-index difference is also paused. On overlapping
windows, both phases approximate the same 2^tX within η_n=(8√5/n)5^(-n/8),
so their character ratio differs from 1 by at most 2π|h|(η_n+η_m).
Cancelling common CRT primes therefore leaves near-maximal correlations,
not the saving needed by correction-index van der Corput. This diagnoses
that argument only, not the original sum. Reopen only with control retaining
cancellation between different physical times; further common-time transport
identities do not supply it. Status: proof sketch, independently reviewed.

Retain the actual-π approximation improvement and this explicit control.
Do not treat further tail precision as the missing digit information.
The correction still freezes a rational approximant; it does not establish
the requested continuing-update mechanism. The unproved step is cancellation
on the short rational orbit carrying the actual accumulated numerator.
No binary or decimal occurrence conclusion for π follows.
