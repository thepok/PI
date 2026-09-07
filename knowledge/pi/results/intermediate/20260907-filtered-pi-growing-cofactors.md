# Growing cofactors in a filtered π/4 series

Status: **proof sketch**. Independent mathematical review and coordinator
inspection completed. Not Lean-verified; no novelty or π digit claim.
This extends the fixed-prime-support applications by verifying growing
cofactors in a specific filtered π representation. The orbit method itself
is classical. The filtered constants are not π.

## The specified family

For positive odd k define ε(k)=1 for k≡1,3 (mod 8), ε(k)=−1 otherwise,
δ(k)=(−1)^((k−1)/2), and

    f₁(k)=ε(k)/(k 2^((k+1)/2)),   f₂(k)=δ(k)/(k 2^(k+1)).

For an integer K≥1 let D_h=K+floor(h/2), and put

    S_K={d3^h : h≥0, 1≤d≤D_h, gcd(d,6)=1},
    ζ_K=Σ_{k∈S_K}(f₁(k)+f₂(k)).

Every finite binary word occurs infinitely often in ζ_K, and

    |ζ_K−π/4| ≤ 4/(K+1) · 2^(−K/2).

Both claims refer to this exact family, not freely chosen normal
approximants. Absolute convergence follows from geometric domination.
To identify the unfiltered sum, expand −Log(1−z) at z=(1+i)/2.
Odd powers give f₁, powers twice an odd integer give f₂, and powers
divisible by four are real. The imaginary part of −Log((1−i)/2) is π/4.
This uses the [standard logarithm series](https://dlmf.nist.gov/4.6.E1).
Every odd k≤K belongs to S_K; summing absolute values at all odd k>K gives
the stronger bound (2^(−K/2)+2^(−K)/3)/(K+1). No monotonicity of ζ_K is used.

## Arithmetic anchors and both update schedules

Let q_j=3^j, M_j=(q_j+1)/2, and

    L_j=lcm{d≤D_j : gcd(d,6)=1},
    P_j=Σ_{k∈S_K,k≤q_j}f₁(k)+Σ_{k∈S_K,k≤(q_j−1)/2}f₂(k).

The truncation is by individual binary exponent, not by whole pairs.
For every included k=d3^h, h≤j and d divides L_j. Therefore

    2^M_j P_j=A_j/(L_j3^j),    A_j≡L_j (mod 3).

Only f₁(3^j) has the full denominator power 3^j, and its sign is positive.
All other included terms contribute a numerator divisible by three.
Updates themselves need not be unique: f₂(1) and f₁(3) coincide, for example.
After g_j=gcd(A_j,L_j) cancels, the reduced denominator Q'_j satisfies

    Q'_j=(L_j/g_j)3^j,    3^j≤Q'_j≤L_j3^j.

Let E_j be the least individual update exponent greater than M_j.
For a future first-type term d3^h with h≤j, odd parity gives its gap at
least 3^h>q_j/D_j. For a future second-type term set a=3^(j−h).
Its gap is ((2d−a)3^h+1)/2; positivity forces 2d−a≥1, hence the gap is
greater than q_j/(4D_j). Terms with h>j have k≥3q_j and larger gaps.
Thus E_j−M_j>q_j/(4D_j), including future newly permitted cofactors.

Put R_j=q_j/(8D_j), H_j=floor(R_j). At most two terms occur at each binary
exponent, each with coefficient of absolute value at most one. Consequently

    sup_{0≤t<H_j} 2^(M_j+t)|ζ_K−P_j| ≤ 4·2^(−R_j).

The elementary LCM bound gives L_j≤4^D_j≤4^K2^j. For clarity, if
U(n)=lcm(1,…,n), U(2m)/U(m) divides binom(2m,m), and
U(2m+1)/U(m+1) divides binom(2m+1,m). Each quotient is squarefree:
at most one new power of each prime lies in the respective interval.
Its factorial-valuation summand is one, all other summands nonnegative.
The bounds binom(2m,m)≤4^m and binom(2m+1,m)≤4^m prove U(n)≤4^n
by induction; the second uses the two equal central coefficients.

## Uniform composite-modulus estimate

For j≥1, gcd(L,6)=1, 3∤A, Q=L3^j, 1≤H≤3^j, and an interval I⊂[0,1),

    |#{0≤n<H : {A2^n/Q}∈I}−H|I|| ≤ 3√Q(1+log Q)².                 (1)

Here and below intervals are half-open. The constant is independent of L.
A complete proof mechanism, including the uniformity issues, is as follows.

A primitive nonprincipal character of conductor f has Gauss sums √f at
unit frequencies and zero at nonunit frequencies. The latter follows by
acting with a unit in the kernel of reduction modulo f/gcd(v,f);
primitivity makes some such character value nontrivial. Parseval proves
the magnitude. Additive Fourier completion then bounds every interval sum
by √f(1+log f). For an induced nonprincipal character modulo odd Q,
inclusion-exclusion over R=∏_{p|Q,p∤f}p costs 2^ω(R). Since
2^ω(R)≤(2/√3)√R and fR≤Q, every nonprincipal interval sum is bounded by
B_Q=(2/√3)√Q(1+log Q), even with new primes in Q.

The principal character contributes φ(Q)|I| with error ≤2^ω(Q)≤B_Q.
Let t=ord_Q(2) and s=φ(Q)/t, initially with A a unit. Each character of
<2> extends to the full unit group in exactly s ways. Averaging these
extensions bounds every nonzero time-Fourier coefficient of the interval
indicator by B_Q. The zero coefficient is t|I| with error ≤B_Q: its one
principal extension must be retained. Time-Fourier inversion yields

    |count−H|I|| ≤ B_Q(H/t+1+log t)

for arbitrary H, since complete periods cancel in nonzero frequencies.
For general A, cancel gcd(A,L) first. The resulting modulus still contains
3^j, so t≥ord_(3^j)(2)=2·3^(j−1), by v₃(4^m−1)=1+v₃(m).
Thus H/t≤3/2, and weakening back to Q proves (1).

## Occurrence and the missing transfer

Applying (1), with R_j≥2, gives the explicit relative bound

    3√(L_j3^j)(1+log(L_j3^j))²/H_j
      ≤432·2^K(K+j)³(√(2/3))^j →0                 (K fixed).

The shifted tail also tends to zero. A length-ℓ word corresponds to a
binary cylinder of width 2^−ℓ. Count visits to its middle half, whose
distance from either boundary is 2^(−ℓ−2). For sufficiently large j the
relative count error is ≤2^(−ℓ−2) and R_j≥ℓ+5. A rational visit then stays
inside the word cylinder after transfer to ζ_K. Windows escape to infinity
and are disjoint, so each word occurs infinitely often. No global frequency
or normality statement follows.

This provides a concrete growing-cofactor application beyond the
[fixed-support recurrence criterion](20260907-cfinite-digit-criterion.md).
New primes really occur among reduced partial-sum denominators: a prime
p>max(K,3) first enters as d=p, h=2(p−K); at its first first-type update,
no earlier denominator or coincident second-type index contains p.
This does not assert that p survives at every anchor. The general
variable-modulus orbit mechanism already accommodates this application;
it is not a new cancellation principle.

For actual π the remaining problem is quantitative, not continuity.
Writing Δ_K=4·2^(−K/2)/(K+1), transfer with margin 2^(−ℓ−3) would follow from

    2^m Δ_K≤2^(−ℓ−3),
    m≤K/2+log₂(K+1)−ℓ−5.

But even H_j≥1 forces 3^j≥8K and M_j≥4K+1/2. Thus the supplied radius
does not certify transfer at any of these windows. The explicit discrepancy
estimate only becomes sufficient much later, at j exceeding approximately
[2 log 2/log(3/2)]K with positive logarithmic and word-length allowances.
Those positions are exponential in K. These are limitations of the proved
bounds, not lower bounds on actual first occurrences or actual error.
Absolute approximation alone does not even guarantee a common binary prefix
without a dyadic-boundary check.

The concrete next extension toward π is to retain the omitted terms while
proving a sufficiently small *shifted* signed tail at controlled visits, or
to find an actual-π representation with compatible denominator and tracking
scales. Neither is established here. Further constant improvements or more
filtered examples alone do not address this missing estimate. Convergence
ζ_K→π/4 cannot substitute for it. No binary or decimal word claim for π
has been gained.
