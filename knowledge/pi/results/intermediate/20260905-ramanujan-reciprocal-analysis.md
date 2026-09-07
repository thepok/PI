# Ramanujan reciprocal: sharp growth and signed tails

Claim status: `proof sketch`; exact-algebra reproduction: `experiment`.
Date: 2026-09-05. No Lean-formalization or novelty claim.
The reciprocal is zero-free on its full convergence disk, its coefficient
exponential rate is 64, and the multiplier 1-128z supplies a positive tail.
These analytic facts do not supply the weighted divisibility needed for P3.
The arithmetic appendix excludes compatible unbounded blocks for the sign
repair 1-128z and the genuinely cancelling multiplier 1-200z.

## Definitions and retained statements

Let c_n=(6n+1) binom(2n,n)^3, F(z)=sum c_n z^n and
G(z)=1/F(z)=sum rho_n z^n. The classical evaluation F(1/256)=4/pi
gives G(1/256)=pi/4. Define eta_0=1 and
eta_n=rho_n-128rho_(n-1), so (1-128z)G(z) evaluates to pi/8.
This note supplies proof sketches of

- F(z) != 0 for |z|<1/64 and |rho_n|<=64^n for all n>=0;
- rho_n<0 for n>=3 and eta_n>0 for n>=4;
- rho_n ~ -(sqrt(pi)/12)64^n n^(-3/2),
  eta_n ~ +(sqrt(pi)/12)64^n n^(-3/2);
- T_M=sum_(m>M)rho_m/256^m ~ -(sqrt(pi)/36)4^(-M)M^(-3/2);
  S_M=sum_(m>M)eta_m/256^m has the opposite leading sign;
  T_M<0 for M>=2, and 0<S_M<4^(-M) for M>=3.

No exact 2-adic valuation formula is assumed in these statements.

## 1. Elementary complex zero exclusion and coefficient bound

Put x=64z, f(x)=F(x/64)=sum b_n x^n and g=1/f=sum r_n x^n.
Here b_n=c_n/64^n, r_n=rho_n/64^n. The ratio is

    b_(n+1)/b_n = (6n+7)(2n+1)^3 / [8(n+1)^3(6n+1)].

Denominator minus numerator equals 24n(n+1)^2+1>0. Thus b_0=1,
b_n strictly decreases to zero (the limit follows from the central-binomial
asymptotic). Set d_j=b_(j-1)-b_j>0 and D(x)=sum_(j>=1)d_j x^j.
Then sum d_j=1 and (1-x)f(x)=1-D(x). For |x|<1,
|D(x)|<=|x|<1; this excludes complex zeros, not just real zeros.

The coefficients u_n of 1/(1-D) obey u_0=1 and
u_n=sum_(j=1)^n d_j u_(n-j). Induction gives 0<=u_n<=1.
Since g=(1-x)/(1-D), r_n=u_n-u_(n-1) for n>=1, hence |r_n|<=1.
In fact u_n<1 for n>=1 because sum_(j=1)^n d_j<1; thus |r_n|<1
for n>=1. This also justifies the strict transformed tail bound below.

## 2. Dominant singularity and coefficient extraction

Write y(x) = 2F1(1/4,1/4;1;x). The
[Clausen identity](https://dlmf.nist.gov/16.12.E2) gives
sum binom(2n,n)^3(x/64)^n=y(x)^2, hence f=y^2+12xyy'.
The [Euler integral](https://dlmf.nist.gov/15.6.E1), with parameters
1>1/4>0, continues y and f analytically to C minus [1,infinity).
On |x|=1, x!=1, absolute convergence of D gives

    Re(1-D(x)) = sum d_j(1-Re(x^j)) >= d_1(1-Re x)>0.

Radial passage in (1-x)f=1-D excludes boundary zeros away from 1.
The [hypergeometric connection formula](https://dlmf.nist.gov/15.10.E21)
with w=1-x gives

    y=A*2F1(1/4,1/4;1/2;w)+C*w^(1/2)*2F1(3/4,3/4;3/2;w),
    A=sqrt(pi)/Gamma(3/4)^2, C=-2sqrt(pi)/Gamma(1/4)^2, AC=-1/pi.

Therefore f=(6/pi)w^(-1/2)+d+(1/pi)w^(1/2)+O(w), where
d=-A^2/2-6C^2. Its nonzero leading term excludes zeros in a slit
neighborhood of 1. Compactness on the remaining unit circle now supplies
a common indented disk |x|<1+epsilon, |arg(x-1)|>phi, 0<phi<pi/2,
on which g is analytic. This is the complex continuation needed for transfer.

Inverting gives g=(pi/6)w^(1/2)+O(w), with a convergent Puiseux
expansion. After subtracting the analytic integer-power terms,
[singularity analysis](https://algo.inria.fr/flajolet/Publications/FlOd90b.pdf)
gives r_n=-(sqrt(pi)/12)n^(-3/2)(1+O(1/n)). Multiplication by
1-2x reverses the leading singular term and yields the eta asymptotic.
Summing with weights 4^(-m) gives the displayed tails, since
sum_(j>=1)4^(-j)=1/3. In particular lim |rho_n|^(1/n)=64;
no global C*Lambda^n bound with Lambda<64 exists.

## 3. Exact sign onsets by induction

Set q(t)=(6t+1)(2t-1)^3/[8t^3(6t-5)], so q_n=b_n/b_(n-1).
Its derivative is 3(2t-1)^2(12t^2-12t-5)/[8t^4(6t-5)^2]>0
for t>=2, and q_4-q_1=63/9728>0. Thus q_n>q_j for n>=4,
1<=j<n. If fv=1 or 1-2x, subtracting successive coefficient equations
gives, for n>=3,

    v_n = sum_(k=1)^(n-1) v_k b_(n-k-1)(q_n-q_(n-k)).

For r_1=-7/8,r_2=41/512, combine the first two terms as
-b_(n-3)U_n, where

    U_n=(7/8)q_(n-2)(q_n-q_(n-1))-(41/512)(q_n-q_(n-2)).

Exact reduction gives U_n=3P8(n-3)/D8(n), with
D8=2048n^3(n-2)^2(n-1)^3(6n-17)(6n-5) and positive ascending
coefficient vector P8=[95940,508108,1529306,2795373,2948477,
1797616,626040,115632,8784]. Thus U_n>0 for n>=3: the n=3
base case is negative, and all remaining terms are negative by induction.

For e_n=eta_n/64^n, the initial terms are
e_1=-23/8,e_2=937/512,e_3=-861/4096. Combine these terms as
b_(n-4)V_n, where

    V_n=-(23/8)q_(n-2)q_(n-3)(q_n-q_(n-1))
        +(937/512)q_(n-3)(q_n-q_(n-2))-(861/4096)(q_n-q_(n-3)).

Here V_n=3P11(n-4)/D11(n), D11=32768n^3(n-3)^2(n-2)^3(n-1)^3
(6n-23)(6n-5), with positive ascending coefficient vector
P11=[244539576,981843408,2562779172,5175230883,6760542367,
5486363918,2813807241,920957279,189234184,23024952,1436688,30384].
This proves e_n>0 for n>=4 by the same induction. Since
|eta_n|<3*64^n, the positive tail obeys 0<S_M<4^(-M), M>=3.

## 4. Scope for fixed polynomial multipliers and P3

For a nonzero fixed P in Z[z], write P(z)=(1-64z)^k Q(z),
Q(1/64)!=0. The same transfer gives

    [z^n](PG) = D_P*64^n*n^(-k-3/2)(1+O(1/n)),
    D_P=pi*Q(1/64)/[6*Gamma(-k-1/2)] != 0.

Thus finite polynomial cancellation changes the power of n and possibly
the sign, but not the exponential rate. The tail is
(D_P/3)4^(-M)M^(-k-3/2)(1+O(1/M)). Its evaluated constant is
(pi/4)P(1/256); it is pi/q for integer q>0 only if q=4/P(1/256)
is such an integer. The multiplier 1-128z has q=8.

For B=10^8 and a_m=eta_m*5^(8m), the shifted tail at M=n+L is
E_(n,L)=B^n S_M. The explicit sufficient smallness condition is
4^(n+L)>=B^(n+h), which yields 0<E_(n,L)<B^(-h), M>=3.
The asymptotic necessary threshold has linear part
L>(log_4 B-1)n+(log_4 B)h, up to an O(log(n+L)) correction.
Here log_4 B is about 13.2877. This does not establish any compatible
divisibility block B^L | sum_(r=1)^L a_(n+r)B^(L-r).
The unmultiplied family has negative tails for all n,L>=1 and cannot
satisfy this positive-tail certificate. Neither fact decides unrestricted P3.

## Reproduction and status boundary

The inspected [audit script](../../../../workflows/experiments/ramanujan_reciprocal_audit_20260905.py)
was independently rerun locally with --n 1000 --precision 80. The exact
symbolic identities for monotonicity, U, V and the local expansion passed,
as did the integer coefficient recurrence and sign/bound scans through 1000.
The first coefficients are rho=(1,-56,328,-13120,-249304,-14947264,...)
and eta=(1,-184,7496,-55104,1430056,16963648,...).
Floating-point asymptotic diagnostics are not interval-certified.
The finite scan is not the infinite proof: the latter uses the induction
and analytic arguments above. No Lean files or manuscript labels changed.

## Arithmetic appendix: exact block valuations and compatibility

Write v=nu_2 (v(0)=infinity), s=s_2. Legendre's factorial identity gives
v(c_m)=3s(m). In the composition expansion of 1/F, each product has
valuation at least 3s(m); a binary carry adds at least 3. In a carry-free
composition, positive parts have disjoint binary supports and are distinct.
For length k>=2, grouping permutations contributes the even factor k!.
Only the length-one term survives modulo 2^(3s(m)+1). Thus
rho_m congruent to -c_m modulo 2^(3s(m)+1), and v(rho_m)=3s(m).
This is an independent proof sketch of the previously supplied valuation,
not a claim that the missing T216 Lean tasks have been completed.

For M=n+L, n>=0,L>=1, the unmultiplied weighted block is
5^(8M)W, where W=sum_(j=0)^(L-1)256^j rho_(M-j).
For j>=1, its jth term has valuation above that of rho_M by at least
8j-3s(j)>=5j>0. Therefore v(W)=3s(M) exactly, and B^L divides
the decimal-weighted block if and only if 8L<=3s(M).
Also v(128rho_(m-1))-v(rho_m)=4+3v(m)>0 for m>=1, so the
same coefficient and block valuation holds for eta. Since s(M)<=log_2(M+1),
admissible L is at most (3/8)log_2(M+1), and M~n as n tends to infinity.
For eta, the proved positive-tail asymptotic then gives

    E_(n,L) >= C*(B/4)^n*M^(-3/2)*(M+1)^(-3/4) -> infinity

along every admissible unbounded sequence, for a fixed C>0 eventually.
Thus its sign repair cannot supply positive-small-tail certificates at
unbounded scales. The original family already fails positivity.

For arbitrary fixed P, put Q=G/(1-256z)=sum q_m z^m and
H_P=PQ=sum h_m z^m. The same minimum argument gives v(q_m)=3s(m),
including m=0. With sigma_m=[z^m]PG, the exact block identity is
W_(n,L)^P=h_M-256^L h_n. Consequently decimal block divisibility is
equivalent to v(h_M)>=8L. A coefficient spike in sigma_M is not enough.
If p_0!=0 and v(p_j)>v(p_0)+3s(j) for each nonzero p_j, j>=1,
the minimum is unique, v(h_M)=v(p_0)+3s(M), and the same logarithmic
obstruction holds. Fixed polynomial singularity cancellation from section 4
does not overcome it. This assertion is restricted to the stated class.

### A genuine cancellation calculation: 1-200z

This lies outside that strict class. It represents 7pi/128; its value at
1/64 is -17/8, so the tail is eventually positive by section 4.
The following exact coefficient identity uses the literal Ramanujan data:

    c_m-56c_(m-1)=8c_(m-1)*(m-1)*(6m^3-23m^2+m+1)/[(6m-5)m^3].

For odd m>=3 all denominator factors and the cubic are odd. Its valuation
is 3s(m)+v(m-1). Put D=(1-256z)F=sum d_m z^m, d_1=-200.
We have v(d_m)=3s(m), and
d_m-d_1d_(m-1)=c_m-56c_(m-1)-51200c_(m-2).
For odd m>=3, t=v(m-1), the last term has valuation 3s(m)+3t+5,
so the difference still has exact valuation 3s(m)+t.

Here is the cancellation-preserving inversion argument. Write
D(z)=E(z^2)+zO(z^2). The odd part of (1+d_1z)/D is
z*(d_1E(z^2)-O(z^2))/(E(z^2)^2-z^2O(z^2)^2).
Let V_k=d_1d_(2k)-d_(2k+1); V_0=0 and
v(V_k)=3s(k)+4+v(k) for k>=1. If J(w)=1/(E(w)^2-wO(w)^2),
then J(z^2)=D(z)^(-1)D(-z)^(-1). Pairing distinct coefficient terms
gives v(J_i)>=3s(i)+1 for i>=1, while J_0=1. For 0<i<k,
binary addition gives c=s(i)+s(k-i)-s(k)>=max(0,v(k)-v(k-i)).
Thus v(J_i V_(k-i))-v(V_k)>=1+3c+v(k-i)-v(k)>=1.
The i=k term vanishes, so V_k is the unique minimum in the odd
coefficient convolution. Even coefficients follow by strict comparison.
Applied to H_(1-200z)=(1+d_1z)/D, this yields

    h_0=1, h_1=0;
    v(h_m)=3s(m) for even m>=2;
    v(h_m)=3s(m)+v(m-1) for odd m>=3.

For L>=2, 256^L h_n has strictly greater valuation than h_M.
For even M, use 8L-3s(L)>0. For odd M, t=v(M-1): if L-1<2^t,
binary subtraction gives s(M-L)-s(M)=t-s(L-2)-2, so the gap is at
least 8L+2t-3s(L-2)-6>0. Otherwise t<=log_2(L-1) and the gap
is at least 8L-3s(L)-t>0. The h_n=0 case is automatic.
Thus every such whole block has the displayed valuation of h_M, bounded by
3 floor(log_2 M)+4. At M=2^k+1 it equals k+6: the cancellation gain
is genuinely unbounded, but only logarithmic. Choosing
L=floor((k+6)/8), n=M-L, k>=10 gives actual divisible blocks, not
compatible small tails. Their scaled positive tails diverge as above.
The sole endpoint M=1 has h_1=0 and yields no unbounded family.

No bound for every fixed polynomial is asserted. For example, for 1-8z,
the h_m valuation is 3s(m) at even m and
3s(m)+min(v(m-1),3) at odd m>=3 with v(m-1)!=3, but this argument
does not bound the extra cancellation at m congruent to 9 modulo 16.
Its actual dominant tail remains negative, so that polynomial itself does
not fix the positive-tail requirement. No P3 or CW0 disproof follows.

The inspected [weighted-block experiment](../../../../workflows/experiments/ramanujan_weighted_blocks_audit_20260905.py)
was rerun locally: all 44,850 blocks with 2<=L<=M<=300 obeyed the
1-200z formula. Its four 1-8z coefficient/block valuation diagnostics
also reproduced exactly. The infinite conclusions use the arguments above,
not those finite checks.
