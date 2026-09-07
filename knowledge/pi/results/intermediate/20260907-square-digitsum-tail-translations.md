# Square digit sums: occurrence through full-tail translations

Status: **proof sketch**. The coordinator checked the argument and three
separate audits covering the tail identity, occurrence argument, and control.
An additional independent GPT-6 Pro whole-proof review completed on 2026-09-07;
the coordinator checked its full argument against this note. No substantive
correction was required; the rational control and witness scope are explicit.
No Lean verification, novelty claim,
normality claim, or digit conclusion for π. Finite checks are not the proof.

## Statement and exact recurrence

Define s(0)=0, s(2m)=s(m), s(2m+1)=s(m)+1, the binary digit sum, and

    u_n=s(n²), P_0=0, P_n=P_(n−1)+u_n2^(-n),
    X=Σ_{n≥1}s(n²)2^(-n).

The claimed conclusion is that every finite binary word occurs infinitely
often in the fractional binary expansion of X. It does not assert normality
or positive lower frequency. The empty word is vacuous. Terminating binary
expansions use zero tails; the argument itself excludes a rational X.

Since s(n²)≤2n, the series converges absolutely. Its exact head and tail are

    Y_n=2^nP_n ∈ Z, R_n=Σ_{j≥1}u_(n+j)2^(-j),
    R_(n+1)=2R_n−u_(n+1), {2^nX}={R_n}.

The injections are unbounded integers, not assigned binary output digits.
The rule and initial state do not depend on a target word.

## An independently irrational translation step

Let L=Σ_{j≥1}s(j)2^(-j). Summing the periodic indicator of each binary
position gives, for 0<z<1,

    Σ_{j≥0}bit_r(j)z^j = z^(2^r)/[(1−z)(1+z^(2^r))],
    L=2Σ_{r≥0}1/(2^(2^r)+1).

Here is a self-contained irrationality proof. Write F=L/2. For m≥1 set
A=2^(2^m), D=∏_{r<m}(2^(2^r)+1)=A−1 and
S_m=Σ_{r<m}1/(2^(2^r)+1). The product identity follows by repeated
factorization of x^(2^m)−1. Then DS_m is an integer, and

    1−2/(A+1) < D(F−S_m) < (A−1)/(A+1)+1/A < 1.

For the upper bound use Σ_{r≥1}A^(-2^r)<Σ_{v≥2}A^(-v)=1/[A(A−1)];
the lower bound retains the first omitted term and a strictly positive tail.
If F=p/q were rational with q>0, qD(F−S_m) would be an integer strictly
between q−1 and q once A+1>2q. Thus L is irrational.
This auxiliary irrationality is classical: see
[Golomb (1963)](https://doi.org/10.4153/CJM-1963-051-0) and
[Coons (2013), primary manuscript](https://arxiv.org/abs/1112.5072).
No distribution theorem about L is used.

## Separated supports give a full-tail identity

For k≥1 and M≥6 put

    B=2^M, N_(k,M)=Σ_{i=0}^{k−1}B^(3^i), C_k=k(k+1)/2.

Expanding (N_(k,M)+j)² gives coefficient blocks j² at exponent 0,
2j at exponents 3^i, 1 at exponents 2·3^i, and 2 at exponents
3^i+3^h (i<h). All these exponents are distinct by their ternary
representations. For 0≤j≤M, every coefficient is less than 2^M,
so the corresponding M-bit binary blocks are disjoint. Consequently

    u_(N_(k,M)+j)=C_k+k s(j)+u_j, 0≤j≤M, with u_0=0.

For arbitrary j≥0, subadditivity of binary digit sums applied to the same
integer expansion gives 0≤u_(N_(k,M)+j)≤C_k+k s(j)+u_j. Binary carries
can decrease the total number of ones, never increase it. Hence the
nonnegative integer defect d(j)=C_k+k s(j)+u_j−u_(N_(k,M)+j) vanishes
for j≤M. Sum the real tails before taking fractional parts:

    R_(N_(k,M))=C_k+X+kL−δ_(k,M),
    0≤δ_(k,M)≤ε_(k,M)=[C_k+(k+2)(M+2)]2^(-M).

Indeed δ=Σ_{j>M}d(j)2^(-j), s(j)≤j, u_j≤2j, and
Σ_{j>M}j2^(-j)=(M+2)2^(-M). The bound has no dependence on the enormous
N_(k,M) other than the displayed k,M. In particular, for every fixed k,

    dist_(R/Z)({2^(N_(k,M))X},{X+kL})≤ε_(k,M) → 0.

This retains the full integer carry: floor(R_(N_(k,M))) equals
C_k+floor(X+kL−δ_(k,M)). It is not an argument about parities alone.

It also proves X irrational before invoking binary words. If X=a/b were
rational, its doubling orbit and its closure would be contained in the
finite set of multiples of 1/b modulo one. The displayed limits would put
all the distinct points {X+kL} in that finite set, a contradiction.

## Occurrence with explicit margins

For a word of length ℓ≥1 and value 0≤v<2^ℓ, take the middle-half interval
I*=[(v+1/4)2^(-ℓ),(v+3/4)2^(-ℓ)]. By pigeonholing 2^(ℓ+3)+1
multiples of L into 2^(ℓ+3) equal bins, some 1≤q≤2^(ℓ+3) has

    0<η=||qL||<2^(-ℓ−3).

The points {jqL}, 1≤j≤1+floor(1/η), have all circular gaps at most η:
up to translation and reflection they are 0,η,...,floor(1/η)η.
Translation by X preserves these gaps. Thus some k among q,2q,...,K,
where K=q(1+floor(1/η)), has {X+kL}∈I*.

Choose M≥6 so that [C_K+(K+2)(M+2)]2^(-M)<2^(-ℓ−2).
The error cannot cross a boundary of [v2^(-ℓ),(v+1)2^(-ℓ)), so the word
starts at position N_(k,M)+1. The same k works for every larger M,
giving infinitely many distinct occurrences. This also gives a finite
witness bound ≤2^(M3^(K−1)+1) for every word of length ℓ. It is enormous;
no useful global frequency estimate is asserted. Choosing observation
indices to certify a word does not insert that word into the recurrence.

This is an effective prescription, not a practical bound in the word length.
The convergent series with explicit tail bounds compute L and X. Strict
rational interval tests find q; irrationality of η and 1/η allows its floor
to be determined by refinement. The circular-gap argument supplies a k in
the interior of I*, so certified approximations can find one. Finally the
inequality defining M is a finite rational test. Arbitrarily long zero words
at increasing positions in particular imply liminf_n ||2^nX||=0.

## Matched avoiding control and nonquiet updates

Use v_n=2+2s(n−1)−s(n)=1+s(n−1)+v₂(n), where v₂ is the exponent of 2.
These are positive integer injections, O(log(n+1)), with v_(2^r)=2r+1.
Starting at zero, their partial sums telescope to

    P̃_n=Σ_{j=1}^n v_j2^(-j)=2−(2+s(n))2^(-n),
    X̃=2, R̃_n=2+s(n)∈Z.

The fractional expansion avoids 1. At the same observation positions,
v_(N_(k,M)+j)=k+v_j for 1≤j≤M; the translation profile is constant 1,
whose weighted sum is rational, rather than the irrational L. In fact
R̃_(N_(k,M))=2+k exactly. Thus this control fails the decisive irrational
full-tail translation property, while retaining positive unbounded updates.
Its limit is rational: this does not supply an irrational avoiding example
with all the remaining properties, and no such stronger separation is claimed.

For the positive example, L≤2 and X≤4 give

    (u_(N_(k,M)+1)/2)/R_(N_(k,M))
      ≥(C_k+k+1)/[2(C_k+2k+4)] > 1/5.

The very next injection remains significant. A frozen P_N has fractional
orbit identically zero from position N onward; it cannot supply the proved
nonzero words. The proof instead approximates a translated *irrational full
tail*, not a rational partial sum. Observation indices are sparse, but
updates occur at every index, and the entire omitted suffix is bounded.

## Exact π assessment: direct transfer fails quantitatively

For the exact π/4 stream in the [full-π note](20260907-full-pi-tail-correction.md),

    σ_e=(-1)^floor((e−1)/2),
    u_e^π=σ_e/(2e−1)+1_(2|e)σ_e/(e−1),
    π/4=Σ_{e≥1}u_e^π2^(-e),

the integer-head property fails already at Y₂^π=10/3. More decisively,
|u_e^π|≤3/[2(e−1)] for e≥2 implies

    |R_n^π|≤Σ_{j≥1}3·2^(-j)/[2(n+j−1)]≤3/(2n).

Thus these tails tend to zero in R and on the circle R/Z. (Their ordinary
fractional parts need not tend to zero when the tails are negative.) A
literal family R_(N_(k,M))^π modulo integers converging to π/4+kL for
every k cannot hold with irrational L: the limits would all be zero, and
subtracting two consecutive k would force L to be integral.

The noninteger head still carries the missing digit information through
{2^nπ/4}={Y_n^π+R_n^π}. A joint head–tail replacement for the displayed
translation identity is not established. This is a quantitative failure of
direct import into this exact π representation, not a general impossibility
claim, and no binary or decimal occurrence result for π follows.
