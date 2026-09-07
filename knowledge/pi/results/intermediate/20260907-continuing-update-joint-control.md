# Continuing updates: marginal distribution does not force digits

Status: **proof sketch**. Full derivation inspected by the coordinator;
separate audits checked arithmetic, harmonic-head cancellation, weighted-tail
cancellation, avoidance and scope. Not Lean-verified; no novelty claim.
This is a control against a proposed inference, not a positive digit theorem.

## One exact rational-output construction

Let t₀=0, t_(2m)=t_m, t_(2m+1)=1−t_m, and σ_m=(−1)^t_m.
Let H₀=0, H_n=H_(n−1)+1/n, v_n=nH_n, r₀=0, and for n≥1 set

    c_n=floor(3^(n−1){v_n}), r_n=(3c_n+1)/3^n,
    u_n=3+t_(n−1)+r_n−2r_(n−1),
    X=Σ_{n≥1}u_n2^(−n), P_n=Σ_{k≤n}u_k2^(−k),
    Y_n=2^nP_n, R_n=2^n(X−P_n).

Every operation uses a fixed arithmetic rule and exact rational division.
The class includes integer quantization and an automatic sequence; it is
not a rational-function-of-n class. Here 1<u_n<5, so updates never stop.
The numerator of r_n is 1 modulo 3 and
|r_n−{v_n}|≤2·3^(−n). Telescoping gives

    X=3+τ, τ=Σ_{n≥1}t_(n−1)2^(−n),
    Y_n=K_n+r_n, R_n=3+τ_n−r_n,
    K_n=Σ_{k≤n}(3+t_(k−1))2^(n−k)∈Z,
    τ_n=Σ_{j≥1}t_(n+j−1)2^(−j).

Both den(u_n) and den(Y_n) equal 3^n in lowest terms: the coefficient
numerator is (3+t_(n−1))3^n+a_n−6a_(n−1)≡1 mod3, where a_n=3c_n+1;
n=1 is immediate. The corresponding frozen unit orbit modulo3^n is
complete, of length2·3^(n−1), and its interval-count error is at most2.
This does not identify it with the actual continuing orbit.

## Avoidance despite two uniformly distributed marginals

Every adjacent pair t_(2m),t_(2m+1) has opposite digits, so neither000 nor111
occurs. Any eventual even period could be halved; an eventual odd period
2a+1 would imply t_(m+a)=t_(m+a+1) eventually, a contradiction. Thus τ is
irrational. Grouping any suffix into triples gives 1/7≤τ_n≤6/7. In particular
||2^nX||≥1/7 for every n≥0.

Nevertheless, for every fixed nonzero integer h, with e(x)=exp(2πix),

    Σ_{n≤N}e(hY_n)=O_h(√N+log(2N)),
    Σ_{n≤N}e(hR_n)=O_h(N^(15/16)log(2N)).

Here are the essential estimates, not a distribution assumption. The
harmonic asymptotic v_n=n log n+γn+1/2+O(1/n) reduces the head to a smooth
phase with second derivative h/x. On a dyadic interval its exponential sum
is O_h(√N); rational rounding costs O_h(1) in total.

For the tail use Σe(hτ_n−hv_n). The identity

    Σ_{m<2^a}σ_m e(mθ)=∏_{j<a}(1−e(2^jθ))

and the adjacent-factor bound16/(3√3) give, on every integer interval of
length L and uniformly in θ, a bound C L^γ₁, where
γ₁=2−(3/4)log₂3<13/16. Arbitrary intervals are decomposed into at most
two aligned dyadic intervals at each size.

On N≤n<2N choose Q=2^floor(log₂N/16), J=ceil(log₂N/16), L=floor(N^(1/3)).
Truncate τ_n to J bits. Writing n=Qm+s, outside the last J−1 residues,
t_(Qm+s+i)=t_m XOR t_(s+i) for i<J. Hence the truncated exponential is
A_s+B_sσ_m with |A_s|,|B_s|≤1. Truncation and bad residues cost
O_h(N2^(−J)+NJ/Q+J). For the smooth phase in m, curvature is comparable
to Q²/N; the unweighted pieces cost O_h(Q√N) over all residues.
Linearizing on pieces of length L costs O_h(Q²L³/N) per piece. The uniform
σ-bound then yields total O_h(NL^(γ₁−1)+Q²L²). Together the errors are

    O_h(N2^(−J)+NJ/Q+J+Q√N+NL^(γ₁−1)+Q²L²+1)
      =O_h(N^(15/16)log(2N)).

The used second-derivative bound is C(L√λ+λ^(−1/2)) when λ≤|f''|≤C₀λ
and f'' has one sign. One elementary proof removes portions where f' is
within δ=√λ of an integer and applies summation by parts on the remaining
monotone first-derivative intervals. Harmonic replacement costs O_h(1)
per dyadic block. Summing dyadic blocks preserves the displayed bounds.
Fourier approximation of continuous functions, then interval bracketing,
proves uniform distribution of each marginal separately.

But e(hY_n)e(hR_n)=e(hτ_n): the oscillation cancels exactly in the product.
For an explicit certificate, the Fejér kernel of order63 is at most49/256
on[1/7,6/7]. If C_N(h)=N^(−1)Σ_{n=1}^Ne(h(Y_n+R_n)), its expansion gives

    Σ_{h=1}^{63}(1−h/64) Re C_N(h)≤−207/512.

Since the weights sum to63/2, one fixed frequency1≤h≤63 satisfies
Re C_N(h)≤−207/(256·63) on infinitely many cutoffs. Both corresponding
marginal averages still tend to zero. Independence cannot be inferred.

## What remains open

Adding λ/n to u_n yields X_λ=3+τ+λ log2. Removing the displayed telescope
leaves the corrected head K_n+λZ_n, Z_(n+1)=2Z_n+1/(n+1).
For λ≠0 the residual λ/n is not a weighted difference B(n)−2B(n−1)
of a rational function: a finite pole chain has two surviving endpoints,
whereas λ/n has one pole. The same holds for A(n)H_n+B(n), because a
nonzero harmonic coefficient would make H_n a rational function of n;
otherwise A(n)=2A(n−1) forces A=0.

This is only a nondegeneracy check. No sufficient digit theorem or even
irrationality claim for 3+τ+log2 is established here. The uncontrolled
observable remains Σe(hZ_n)e(hτ_n), not either factor separately.
The control does not refute hypotheses restricted to rational-function
forcing, since its quantized automatic generator is outside that class.
Retain it as a test for new joint estimates; do not refine it as an end in
itself. No π digit conclusion follows.

### Bounded joint-differencing follow-up

Status: **proof sketch**, coordinator-inspected; no saving obtained. For
X=3+τ+log2 set a_h(n)=e(hZ_n)e(hτ_n),
T_n=Σ_{j≥1}2^(−j)/(n+j), and W_k(M)=Σ_{n=1}^M e(k2^nX).
Since a_h(n)=e(h2^nX)e(−hT_n), the lag correlation C_h(N;r) satisfies
|C_h(N;r)−W_(h(2^r−1))(N−r)|≤2π|h|log(r+1), uniformly for1≤r<N.
Indeed T_n decreases, and Σ_{n=1}^{N−r}(T_n−T_(n+r))≤Σ_{n=1}^r1/(n+1).
The small error does not bound the correlation: differencing retains the
same unknown joint orbit at higher frequencies. The investigated dyadic
blocking provides no subtrivial estimate. Further work requires a genuine
bound on those signed correlations, not another version of this identity.
