# Polynomial feedback with factorial activation

Status: `proof sketch`; companion checks: `experiment`. An independent mathematical
review has checked the factorial argument below; Lean verification is pending.
No novelty or pi digit claim is made.

Independent review (2026-09-07) rederived convergence, the exact numerator
recurrence and reduced p-part, complete-period grids, circular interval transfer,
and arbitrary-cutoff normality. In the cutoff calculation, include the possible
terminal guard g_n explicitly. The weighted interval errors can be controlled
by splitting off finitely many early windows and using sum of covered lengths
at most N; the absolute period errors are O(p^n)=o(n!). The product controls
also survive review. Here endpoint avoidance means the unit-interval endpoints
0 and 1: the avoiding orbit does accumulate at 2/9. This is independent
proof-sketch review, not machine checking or verification of later extensions.

## Statement under review

Let b >= 2 be an integer, p an odd prime not dividing b, and
F(X)=sum_{j=0}^d f_j X^j an integer polynomial of degree d >= 1.
Choose an integer a with p not dividing f_d F(a). Set
R=|a|+1, M=sum_j |f_j| R^j, and choose an integer K >= 1 with
b^K >= max(2 p^(d-1), 4M/p). Define

\[
m_n=K(n+1)!,\qquad x_0=a,\qquad
x_{n+1}=x_n+p^{(d-1)n-1}b^{-m_n}F(x_n).
\]

The proposed conclusion is that the limit alpha exists and is base-b normal.
The finite hypotheses do not specify any target digit word. The mechanism is
long rational periods, not a new general principle about arbitrary recurrences.

## Proof sketch and the actual digit bridge

1. Write c_n=p^((d-1)n-1)b^(-m_n). The coefficient ratio is at most 1/2,
   and M sum c_n <= 1/2. Induction bounds |x_n-a| <= 1/2, so
   |alpha-x_n| <= C p^((d-1)n)b^(-m_n), where C=2M/p.

2. Put s_0=0 and s_(n+1)=d s_n+m_n. Direct substitution gives
   x_n=P_n/(p^n b^s_n), where P_0=a and

   \[
   P_{n+1}=p b^{(d-1)s_n+m_n}P_n+
   \sum_{j=0}^d f_j p^{n(d-j)}b^{(d-j)s_n}P_n^j.
   \]

   P_1=p b^K a+F(a) is a p-unit, and for n>=1,
   P_(n+1)=f_d P_n^d modulo p. Thus every P_n for n>=1 is a p-unit.
   The p-part of the reduced denominator is exactly p^n. The possibly
   unreduced base-supported factor b^s_n is retained in the estimates.

3. Let tau=ord_p(b) and kappa=v_p(b^tau-1). For n>=kappa, the
   order modulo p^n is T_n=tau p^(n-kappa). The orbit of a p-unit modulo
   p^n consists of tau complete residue classes modulo p^kappa: powers of
   b^tau generate 1+p^kappa Z modulo p^n, by the odd-prime lifting formula.
   Each class, divided by p^n, is an equally spaced grid. Consequently,
   for a circular interval I and any consecutive L terms of any such orbit,

   \[
   |\#\{j:\{A b^j/p^n\}\in I\}-L|I||
   \le 2p^{\kappa-n}L+T_n.
   \]

   The numerator and starting phase are arbitrary p-units and arbitrary
   nonnegative phases. This is a complete-period estimate, not an assumed
   short-orbit cancellation estimate.

4. Set g_n=n+max(0,ceil(log_b(C p^((d-1)n)))) and
   W_n=[s_n,m_n-g_n) intersect Z. At t in W_n,
   |b^t(alpha-x_n)| <= b^(-n), while the fractional part of b^t x_n is
   that of P_n b^(t-s_n)/p^n. Enlarging and shrinking I on the circle gives,
   for any consecutive subinterval J of W_n of length L,

   \[
   |\#\{t\in J:\{b^t\alpha\}\in I\}-L|I||
   \le (2b^{-n}+2p^{\kappa-n})L+T_n.
   \]

   This is the point where a target interval is actually reached. In
   particular every length-ell word occurs within W_n if its right-hand
   error divided by |W_n| is less than b^(-ell).

5. Solving the exponent recurrence gives s_n=K sum_{j<n} d^(n-1-j)(j+1)!.
   Hence s_n <= e^d K n!, g_n=O(n), |W_n|~m_n, and T_n/|W_n| tends to zero.
   For arbitrary cutoffs m_(n-1)<=N<m_n, the total uncovered length is
   O(m_(n-2)+n^2), apart from a fixed initial segment: a gap before W_k
   has length d s_(k-1)+g_(k-1). Dividing by N makes this O(1/n).
   Summing the interval-count errors over the complete and partial windows
   also gives a vanishing relative error (the period errors sum to O(p^n),
   whereas N>=K n!). Thus the proposed conclusion is normality at arbitrary
   cutoffs, not just along the window endpoints.

## Explicit positive and avoiding examples

The nonlinear example b=10, p=3, F(X)=X^2, a=1, K=1 passes the finite
checks (M=4 and 10>=max(6,16/3)). Its proposed limit is decimal-normal.

A comparable degree-one pair is

\[
z_0=2/9,\qquad z_{n+1}=z_n+\frac{z_n+7/9}{q10^{(n+1)!}},\qquad
C(q)=\prod_{n\ge0}(1+q^{-1}10^{-(n+1)!})-7/9.
\]

For q=3 the unshifted product is the degree-one positive case. Subtracting
7/9 leaves the p-unit numerator property unchanged for n>=3, since the
subtracted numerator is 7*3^(n-2)*10^s_n, divisible by 3.

For q=10, let r_n=(n+1)!+1. These exponents are superincreasing. The
product minus 1 has coefficients 0 or 1 at the finite subset sums of the
r_n, without carries. Adding 2/9 therefore gives only digits 2 and 3.
There are infinitely many subset sums and unbounded gaps between them,
so the digit sequence is not eventually periodic and C(10) is irrational.
All its decimal shifts lie in [2/9,1/3], excluding endpoint recurrence.
This control fails the growing base-coprime denominator hypothesis.

## Scope, literature, and next extension

Every positive constant in the factorial class is Liouville: its displayed
denominator is at most p^n b^s_n and m_n/s_n tends to infinity. Irrationality
follows from the proposed normality conclusion. Thus this class cannot
contain pi. Its nonlinearity does not remove the enormous tracking budget.

The rational-period mechanism is established literature, not claimed new:
[Bailey--Crandall, Random Generators and Normal Numbers, Theorem 4.8 and
Corollary 4.9](https://www.davidhbailey.com/dhbpapers/bcnormal.pdf) prove
normality for specified additive sparse series; some use orbit segments
shorter than a period. Those statements do not by themselves verify this
feedback recurrence. Priority for the feedback formulation is unresolved.

The geometric extension replaces m_n by K A^n.
Then s_n=K(A^n-d^n)/(A-d); A>d+1 leaves a nonempty asymptotic tracking
window, and A>p makes complete periods fit. This suggests digit occurrence,
but the factorial proof of global normality no longer applies because the
discarded gaps need not have zero density. The reviewed sections below now
establish digit occurrence and a finite irrationality exponent for a
specified nonlinear example.
Even that would not be a pi bridge: natural pi recurrences have neither the
proved residual prime-power structure nor these long tracking windows.

Reproducible checks: `python3 workflows/experiments/polynomial_feedback_20260907/check.py`.
The script checks finite rational identities, exact residue-class orbits,
and finite avoiding products. It does not prove any infinite assertion above.

## Reviewed critical geometric case (2026-09-07)

Status: `proof sketch`, independently checked recurrence/window algebra and
Pro reconstruction of the subperiod proof; not Lean, not a novelty claim.
The earlier strict geometric condition is sufficient but misses a boundary case.
For K>=1, set x_0=1 and

\[
x_{n+1}=x_n+3^{n-1}10^{-K3^n}x_n^2.
\]

The limit alpha_K exists and every decimal word occurs infinitely often.
Here the exact reduced denominator is
Q_n=3^n 10^{K(3^n-2^n)}: the numerator recursion
P_(n+1)=3*10^(s_n+K3^n)*P_n+P_n^2 preserves units modulo 2,3,5.
Thus s_n=K(3^n-2^n) is the least decimal-clearing shift, not an
overestimate removable by denominator cancellation.

A bootstrap gives 1<=x_n<2 and
0<alpha_K-x_n<=(40/21)3^n10^(-K3^n). Put
g_n=n+ceil(log_10((40/21)3^n)) and W_n=[s_n,K3^n-g_n) intersect Z.
The shifted error on W_n is at most 10^(-n), and
|W_n|=K2^n-g_n>=K2^(n-1) for n>=5. The subleading 2^n term is essential.

For q=3^n, n>=2, the base-10 subgroup is exactly the units equal to 1
modulo 9, with order T=3^(n-2) and index six in the full unit group.
For the interval indicator restricted to any unit coset, each nonzero
Fourier coefficient on this subgroup is bounded by sqrt(q)(1+log q).
Indeed, extend the subgroup character to the full unit group and average
over its six extensions. All six characters are nonprincipal; the
Pólya--Vinogradov bound applies also to imprimitive characters here because
their conductor is a power of the same prime 3, so extending by zero
introduces no additional sieve. Primitive character sums follow from the
Gauss sum identity and finite Fourier inversion. Summing the geometric
Fourier factors costs at most 1+log T, uniformly in segment length and phase.

The zero coefficient must be kept: the coset is a grid of T points, not
Lebesgue measure. Its interval count differs from T|I| by at most 2.
Consequently every consecutive J subset W_n of length L satisfies

\[
\left|\#\{t\in J:\{10^t\alpha_K\}\in I\}-L|I|\right|
\le (2\,10^{-n}+2/T)L+
3^{n/2}(1+n\log3)(1+(n-2)\log3).
\]

Circular enlargement and shrinkage transfer the rational bound, including
the empty/full interval cases. Omitting the 2L/T term for arbitrary L
would be false: repeated full periods retain the finite-grid bias.
Dividing by |W_n| leaves O(n^2(sqrt(3)/2)^n)+O(3^(-n))+O(10^(-n)),
which tends to zero uniformly over target intervals. Each word therefore
occurs in every sufficiently late window. No target digits are inserted
into the recurrence and no distribution hypothesis is assumed.

The union of these windows has density zero: below a cutoff of order 3^n
there are only O(2^n) covered positions. Thus this proof gives neither
normality nor positive global lower word frequency. Also
-log|alpha_K-x_n|/log Q_n tends to 1, so the previous separation argument
requiring an exponent strictly greater than 1 does not give a finite
irrationality exponent. The identity Q_n|alpha_K-x_n|=O(3^(2n)10^(-K2^n))
still proves irrationality by separation from a hypothetical fixed rational.
This improves the admissible update scale of the restricted theory, not
the logarithmic tracking barrier for natural pi approximants.

## Reviewed geometric example with finite irrationality exponent

Status: `proof sketch`. Independent Pro review rederived all interfaces;
separate local audits checked coverage, rational separation, and the pair's
denominators. No Lean or novelty claim. Define

\[
x_0=1,\quad x_{n+1}=x_n+3^{n-1}10^{-6^n}x_n^2,\quad
\alpha=\lim x_n.
\]

Then mu(alpha)=4, and every length-ell decimal word has lower frequency
at least (3/5)10^(-ell), counted by its starting positions. Normality is
not established. Here are the proof ingredients, including arbitrary rationals.

* Convergence follows by the bounded-iterate argument above. Put
  c_n=3^(n-1)10^(-6^n). Then c_n<=alpha-x_n<=8c_n, with strictly
  positive error. The exact reduced denominator is
  Q_n=3^n10^s_n, s_n=(6^n-2^n)/4. The numerator recursion preserves
  P_n=1 modulo 30, so no base-supported denominator factor is discarded.
* For n>=2, W_n=[s_n,6^n-3(n+1)) is nonempty and has length at least
  6^n/2. The complete-period interval bound already proved above gives
  error at most (2*10^(-n)+18*3^(-n))L+3^(n-2) for any consecutive
  subinterval of W_n of length L.
* Compare these windows with ideal intervals [6^n/4,6^n). Covered
  proportions reach their minima at interval starts and maxima at ends.
  Summing their lengths gives limiting proportions 3/5 and 9/10.
  Actual coverage differs by O(2^n+n^2) below a cutoff between 6^(n-1)
  and 6^n, hence by o(N). Summed interval errors are O(3^n+2^n+1)=o(N).
  The covered positions therefore supply at least (3/5)|I|N-o(N)
  visits to each interval I at every sufficiently large cutoff. Nothing
  is asserted about distribution on the remaining positions.
* The exact arithmetic implies log Q_(n+1)/log Q_n -> 6 and
  -log(alpha-x_n)/log Q_n -> 4. Also Q_n(alpha-x_n)->0 and the errors
  are nonzero, which proves irrationality by rational separation without
  using the digit theorem. The approximants give mu(alpha)>=4.
* For the upper bound, fix 0<epsilon<3. Eventually
  Q_n^(-4-epsilon)<=e_n<=Q_n^(-4+epsilon) and
  Q_(n+1)<=Q_n^(6+epsilon), where e_n=alpha-x_n. For an arbitrary
  reduced u/q with q sufficiently large, choose the first sufficiently
  late n with Q_n e_n<=1/(2q). Minimality at n-1 gives
  Q_n<=(2q)^gamma, gamma=(6+epsilon)/(3-epsilon).
  If u/q differs from x_n, separation gives
  |alpha-u/q|>=1/(2qQ_n)>=2^(-1-gamma)q^(-1-gamma).
  If u/q=x_n, exact reduction gives q=Q_n and the lower error bound
  gives |alpha-u/q|>=q^(-4-epsilon). Letting epsilon decrease to zero
  proves mu(alpha)<=max(4,1+6/3)=4. This coincidence case cannot be
  justified using only a denominator upper bound.

### A positive/avoiding pair with the same exponent

Define C(q)=product_(n>=0)(1+1/(q10^(6^n)))-7/9 for q=3,10.
This is the limit of z_0=2/9,
z_(n+1)=z_n+(z_n+7/9)/(q10^(6^n)). Both have mu=5.
Every length-ell word in C(3) has lower frequency at least
(4/5)10^(-ell); C(10) has only digits 2 and 3, with
inf_t ||10^t C(10)||=2/9.

For C(3), the n-factor product has exact denominator
3^n10^((6^n-1)/5); each numerator factor is 1 modulo30.
After translating by -7/9 this remains the exact denominator for n>=3,
since the subtracted numerator is divisible by30. Errors are between
(1/3)10^(-6^n) and (4/3)10^(-6^n). The preceding window proof for
degree one gives coverage lower density4/5, with negligible relative
count errors. Its two logarithmic approximation ratios are6 and5.

For C(10), exponents r_n=6^n+1 are superincreasing, and
r_n-sum_(j<n)r_j=(4*6^n+6)/5-n tends to infinity. Expanding the
absolutely convergent product gives 0/1 coefficients at unique subset
sums. Adding2/9 gives digits2/3 with infinitely many3s and unbounded
runs of2s, proving irrationality and the stated infimum. The shifted
n-factor approximant has exact denominator9*10^S_n,
S_n=(6^n-1)/5+n: the factor9 must not be omitted. Its positive error
lies between10^(-r_n) and3*10^(-r_n). The logarithmic ratios are again
6 and5. The same separation proof for either product gives
5<=mu<=max(5,1+6/4)=5. Thus approximation exponent alone is not the
distinguishing property; the growing off-base denominator is.

These results remove the Liouville restriction from the positive theory.
They still rely on off-base denominators that are small enough for long
rational-orbit tracking, and establish no decimal occurrence for pi.
The rational-separation method is established literature; see
[Adamczewski--Rivoal, Lemma4.1](https://adamczewski.perso.math.cnrs.fr/IMAN.pdf).
Priority for the feedback formulation is not asserted.
