# Sparse prescribed digits and a fixed bad-approximation constant

Claim status: `proof sketch`. Date: 2026-09-05.
For the full base-b shift, every zero-density set of forced positions
admits a full-dimensional intersection with badly approximable numbers.
For each s<1, one positive Markov constant works uniformly over all
assignments on that fixed set of positions. General P1′ remains open.
This is separator mathematics, not CW0, CW9, or V1 for pi; no novelty or
Lean-formalization claim is made.

## Precise partial statement and literature input

Let b>=2, F subset of the positive integers, and f(n)=|F intersect [1,n]|=o(n).
For any assignment d:F->{0,...,b-1}, let K_d be the image of all compatible
base-b streams. Put BA(kappa)={x: |x-p/q|>=kappa/q^2 for every integer p,q,
q>=1}. The retained statement is

```
for every 0<s<1 there exists kappa=kappa(b,F,s)>0 such that
for every d:F->{0,...,b-1}, dim_H(K_d intersect BA(kappa)) >= s.
```

Choose M so that the bounded-continued-fraction set B_M has dimension
delta>max(s,1/2). Its normalized delta-dimensional Hausdorff measure mu
satisfies mu(I)<=C|I|^delta and |mu_hat(k)|<=C(1+|k|)^(-eta), eta>0.
The decay for this *particular Hausdorff measure* is the explicit conclusion
of [Jordan–Sahlsten, Corollary 1.4 and section 6.7](https://arxiv.org/html/1312.3619).
It is not inferred merely from equivalence to a Fourier-decaying measure.
The same paper records dim_H(B_M) increasing to 1. The Frostman estimate
follows from the finite continued-fraction conformal construction: bounded
distortion gives cylinder masses comparable to length^delta, and stopping
cylinders have comparable lengths and separated interiors. Bounded digits
give B_M subset BA(1/(M+2)), by the convergent error formula and Legendre's
criterion for nonconvergents. These literature inputs have not been imported
as unconditional Lean theorems.

## Uniform sparse-mask estimate

Primary precedent (`literature-checked`): [Bourgain, Lemma 1, equation
(2.3)](https://arxiv.org/pdf/1307.0398) bounds the probability-normalized
Fourier l1 norm for arbitrary prescribed binary positions by
2^(C rho log(1/rho)n), where rho is their proportion. His prime application
also fixes the least significant bit; adding that one prescription does not
affect the density-zero consequence. The proof groups complementary free
runs. The all-base estimate below and rational-slicing assembly are
deductions, not a BA theorem stated by Bourgain. This antecedent rules out
treating the independent sparse-mask estimate itself as a new ingredient.

On the circle, E_n is the union of compatible half-open length-n cylinders,
g_n=b^f(n) 1_(E_n), and nu_n=g_n dx is a probability measure. Digits are
independent, deterministic at forced positions <=n and uniform elsewhere.
For every epsilon>0,

```
sup_n sum_(|k|<=T) |nu_n_hat(k)| <= C_epsilon (1+T)^epsilon.        (1)
```

Here and below the constants are independent of d. To prove (1), group
digits into length-L blocks, B=b^L. Write m_j for the probability mask of
block j; nu_n_hat(k)=product_(j>=1) m_j(k/B^j). A block is dirty if it
meets F (even when its forced position is beyond n). Among the first J,
r_J<=f(LJ)=o(J), for fixed L. The uniform clean mask U_B satisfies

```
Lambda_B = sup_t sum_(a=0)^(B-1) |U_B(t+a/B)| <= C log(2B),
sup_t sum_(a=0)^(B-1) |m_j(t+a/B)| <= B  for any probability mask.
```

The first estimate follows from |U_B(t)|<=min(1,1/(2B||t||)) and the
harmonic sum over a uniformly spaced grid. In the partial product sum
S_J=sum_(k=0)^(B^J-1) product_(j=1)^J |m_j(k/B^j)|, write
k=k'+a B^(J-1). The earlier factors are unchanged, so
S_J<=Lambda_B^(J-r_J) B^r_J. Dropping later factors only increases the
bound for |nu_n_hat(k)|. First choose L with log_B Lambda_B<epsilon/2,
then use r_J/J<epsilon/2 eventually. Enlarging a constant handles the
finitely many smaller J and arbitrary T. This proves (1), including the
uniformity in n and all forced words. In particular, for epsilon<eta,

```
sup_n sum_(|k|>=T) (1+|k|)^(-eta)|nu_n_hat(k)|
  <= C_(epsilon,eta) T^(epsilon-eta).                            (2)
```

## A fixed rational slice, with dimension at every scale

Set h_n(t)=integral g_n(t-x) dmu(x). Its Fourier coefficients are
mu_hat(k)nu_n_hat(k), with uniformly absolutely summable tails by (2).
Because g_n is a finite step function and mu is atomless, h_n is continuous;
thus its Fourier representation holds at every t, not just almost everywhere.
Choose an integer c>=2 for which the uniform tail above |k|>=c is <1/2.
Then the exact rational-grid average satisfies

```
(1/c) sum_(a=0)^(c-1) h_n(a/c)
  = sum_(ell in Z) mu_hat(c ell)nu_n_hat(c ell) > 1/2.             (3)
```

Fix kappa=1/((M+2)c^2) now, before choosing a slice. One of these finitely
many a has h_n(a/c)>1/2 along infinitely many n. For this fixed t=a/c,
the measures rho_n=g_n(t-x)mu have uniformly bounded mass and, along that
subsequence, mass >1/2.

To preserve dimension, take a smooth bump phi_I>=1 on an interval I of
length r, supported in an O(r) enlargement. The two estimates

```
|(phi_I mu)_hat(k)| <= C r^delta,
|(phi_I mu)_hat(k)| <= C r^(-eta)(1+|k|)^(-eta)
```

follow respectively from Frostman and convolution with the smooth bump's
Fourier coefficients, whose weighted l1 norm is O(r^(-eta)). Pairing with
g_n and splitting at T gives

```
rho_n(I) <= C_epsilon [r^delta T^epsilon
                         + r^(-eta) T^(epsilon-eta)].           (4)
```

This pairing is valid pointwise: convolution of phi_I mu with g_n is
continuous, and the Fourier series is absolutely convergent. Equivalently,
use Fejer means of each fixed g_n: they are bounded by its finite supremum
and converge away from finitely many endpoints, which have zero phi_I mu
mass for every translate. Dominated convergence and absolute Fourier
summability justify the pairing; no supremum bound uniform in n is needed. Set
A=1+delta/eta and T=r^(-A). Both powers in (4) are delta-A epsilon.
For each 0<u<delta choose epsilon small enough, obtaining the uniform
all-scales bound rho_n(I)<=C_u |I|^u. It passes to a weak limit rho through
open intervals and then arbitrarily small interval enlargements. The limit
has positive mass, and consequently its support has dimension >=delta.

The closed compatible cylinder sets K_(d,n) are nested. For every fixed m,
late rho_n are supported in B_M intersect (t-K_(d,m)); hence rho is supported
in B_M intersect (t-K_d). Nested symbolic compactness justifies the last
intersection even at endpoints with two expansions. For x in this support,
y=t+j-x in [0,1) satisfies

```
|y-p/q| = |x-(a q+j c q-c p)/(c q)| >= 1/((M+2)c^2 q^2).
```

Reflection modulo one is piecewise isometric. The reflected support lies
in K_d intersect BA(kappa) and has dimension >=delta>s. Its irrationality
automatically excludes the countable ambiguous radix endpoints. All
constants fixing c were independent of d, proving the stated uniformity.
No kappa tends to zero along the limiting construction.

## Reduction of the remaining finite-type problem

For a canonical finite-memory graph of a nonempty SFT with compatible
forcing, call a strongly connected component C admitted if a compatible
infinite path eventually stays there. If lambda_C is its adjacency spectral
radius, zero-density forcing implies

```
dim_H(K_(Sigma,F)) = max_(C admitted) log_b(lambda_C).            (5)
```

For the upper bound every path eventually stays in one component, and there
are only countably many finite entry prefixes. For the lower bound fix a
compatible reference path eventually in C. If C has period p, choose large
fixed L divisible by p and fix block boundary states to those of the reference.
Perron–Frobenius gives at least R_L=floor(a_C lambda_C^L) paths between any
such states in the same cyclic class, with a_C>0 independent of L. Freeze
dirty blocks to the reference and independently choose among clean paths.
Only o(J) of the first J blocks are dirty. Cylinder masses are at most
R_L^(-J+o(J)); unfinished blocks have fixed length L. The all-scales
dimension is at least log_b(R_L)/L, which tends to log_b(lambda_C).
Zero-entropy components contribute zero. The canonical presentation makes
distinct paths from a fixed state distinct digit words.

Thus an entropy-neutral corridor in a general SFT admits a maximal-entropy
component; irreducible corridors are automatically entropy-neutral. A fixed
entry prefix x=(P+y)/b^m transfers BA(kappa_y) to BA(kappa_y/b^m).
Grouping p digits removes periodicity: prescribe each grouped digit touched
by forcing to equal its reference value. Grouped forced positions still
have density zero, and (5) retains full component dimension in this subset.
The remaining universal P1′ case is therefore proper positive-entropy
mixing SFTs, not reducibility or periodicity. Their clean masks are not
uniform; (1) cannot simply be assumed for a measure on a set of dimension
<1. Indeed (1) and |nu_hat|<=1 would imply finite u-energy for every u<1.

## Reproduction and scope

The inspected [finite audit](../../../../workflows/experiments/p1prime_fourier_audit_20260905.py)
compares digit products against direct cylinder integration, checks the
radix-block transfer identity, and checks all-scales density bounds for
N_j=2^(j^2), ell_j=floor(N_j/j). Local rerun passed: the largest Fourier
coefficient discrepancy was <6e-15 and transfer discrepancy <1.3e-12.
Those checks use floating-point arithmetic; the schedule inequalities use
exact rational arithmetic. All are `experiment`, not proof of the infinite
assertions or certified Fourier constants. The analytic argument above was
independently inspected; it remains `proof sketch`, and universal P1′ for
proper mixing SFTs and every pi-specific digit target remain `conjecture`.

## Restricted P1-PD/NE for sufficiently long forbidden zero words

Claim status: `proof sketch`, independently audited and corrected 2026-09-05.
For every 0<s<1 there is L0(s)>=2 such that, for every L>=L0(s),
every marker c in {1,...,8}, and every finite prefix P avoiding 0^L,
there is kappa>0 with
dim_H(C_(0^L) intersect I(P) intersect ALA_({1,...,9},c)
      intersect BA(kappa)) >= s.
This gives restricted P1-PD/NE instances, not their universal versions,
not full dimension for a fixed L, and not a digit property of pi.

### Proper-shift estimate supplying the corollary

Let Sigma_L forbid 0^L in base b>=2, L>=2. Its states u=0,...,L-1
record the trailing zero-run: 0 sends u to u+1 when u<L-1; each nonzero
digit resets to 0. Let lambda solve 1=(b-1)sum_(j=1)^L lambda^(-j),
and h_u=(b-1)sum_(j=1)^(L-u)lambda^(-j). Then h_0=1 and
gamma=(b-1)/b<=h_u<=1. Put B=b^L and R_b=gamma^(-2).
For the fixed continued-fraction measure above use 0<eta<delta<1, and set

```
A_(b,L) = R_b b L (b/lambda)^L (2+L log b),
theta_(b,L) = log(A_(b,L))/(L log b).
```

For any fixed zero-density F and theta_(b,L)<alpha<eta, the retained
partial bound, uniform over all compatible assignments on F, is

```
dim_H(pi_b((Sigma_L)_F) intersect BA(kappa))
  >= u = delta(1-alpha/eta),   for one kappa>0.                 (6)
```

The following supplies the nonstationary estimate needed to apply the
earlier rational-slice argument; stationary Parry decay is not assumed.
A length-L digit word, interpreted as an integer a, goes from state u
to state v precisely when

```
a in A_uv = {a: b^u<=a<B, b^v divides a, b^(v+1) does not divide a}.
N_uv = |A_uv| = (b-1)(b^(L-v-1)-1_(u>v)b^(u-v-1)).
```

The lower bound on a excludes a leading zero-run completing the incoming
run, and the valuations prescribe the trailing run. A full internal 0^L
would make the entire block zero, already excluded. Each such path has
Parry probability lambda^(-L)h_v/h_u. Thus the L-step matrix
P_uv=lambda^(-L)(h_v/h_u)N_uv is positive and stochastic, with
R_b^(-1)<=P_uv/P_(u'v)<=R_b. For every nonzero H>=0,
max(PH)/min(PH)<=R_b.

For each horizon n, condition this process (starting at state 0) on all
forced digits through nL, then append independent uniform digits. This
gives a finite step density g_n and nu_n=g_n dx. With H_j the backward
likelihood of satisfying blocks j,...,n, H_(n+1)=1, its block-word kernel is

```
Q_j(u,w,v) = chi_j(w) lambda^(-L)(h_v/h_u) H_(j+1)(v)/H_j(u),  (7)
```

where chi_j is the indicator that w satisfies the current block's forcing;
set the row to zero if H_j(u)=0. The indicator is indispensable: at b=L=2,
forcing the first digit to be 1 makes the probability of 01 zero, whereas
omitting chi_j would give lambda^(-1)>0. The independently audited formula
(7) corrects that omission in the proposed derivation; the finite script
already included the indicator.

If both j and j+1 are clean, H_j=PH_(j+1), H_(j+1)=PH_(j+2), so
H_(j+1)(v)/H_j(u)<=R_b. The final clean block has ratio 1. Treat all
blocks touching the original infinite F, and their immediate predecessors,
as exceptional. Their count r_J<=2f(L(J+1))=o(J), independently of n.

For the Fourier bound, A_uv is a union of b-1 arithmetic progressions
a=b^v(d+bz), each a terminal interval in z. The shifted Dirichlet estimate

```
sup_t sum_(ell=0)^(Q-1) |sum_(z=A)^(A+N-1) exp(-2pi i z(t+ell/Q))|
  <= Q(2+log Q),  0<=N<=Q,
```

follows by ordering the grid's distances to integers: the j-th distance is
at least (j-1)/(2Q), leaving one Q term and a harmonic sum. Applying it to
the progressions and summing over terminal states bounds the shifted
row l1 norm of an unconditioned block mask by
bL(b/lambda)^L(2+L log b). The likelihood ratio adds at most R_b on
nonexceptional blocks; exceptional blocks have the trivial B bound.
After the horizon, use the uniform scalar mask times the identity, which
also satisfies these bounds. All masks contract the row l1 norm.

In k=k'+ell B^(J-1), earlier matrix factors are unchanged. For a row z,
sum_ell ||z M(t+ell/B)||_1<=sum_u |z_u|sum_(ell,v)|M_uv(t+ell/B)|;
there is no extra factor from the number of states. Run the induction on
sum_(0<=k<B^J) ||e_0 M_1(k/B)...M_J(k/B^J)||_1, not on the absolute
value after multiplying this row by the all-ones column: that scalar can
have cancellations invalidated by a state-dependent continuation.
The actual continuation column has sup norm at most 1, so the row-norm
estimate bounds the full Fourier coefficients. Induction gives

```
sum_(0<=k<B^J)|nu_n_hat(k)| <= A_(b,L)^(J-r_J) B^r_J.
D_alpha = max(0,sup_(J>=1)[r_J-(alpha-theta_(b,L))J]) < infinity,
sup_n sum_(|k|<=T)|nu_n_hat(k)| <= C_nu T^alpha,  T>=1,
C_nu = 2 B^(D_alpha+alpha).                                    (8)
```

This includes horizons shorter than the frequency scale and scales inside
forced packets. It is uniform in the forced values, not a subpolynomial
bound for a proper shift.

### Localization, the real dimension loss, and one fixed constant

For a fixed-profile smooth bump phi_I on a length-r interval,
|phi_I_hat(ell)|<=C_N r(1+r|ell|)^(-N). Splitting the convolution with
mu_hat into |ell|<=|k|/2, |ell|>|k|/2 with |k-ell|<=2|k|, and the
remaining tail gives, when |k|>=1/r, the bound C|k|^(-eta).
For the middle region use sum_(|m|<=2|k|)(1+|m|)^(-eta)=O(|k|^(1-eta));
its contribution is O(|k|^(-eta)(r|k|)^(1-N)). The other regions satisfy
the same bound. Below 1/r the Frostman estimate and delta>eta apply. Hence

```
|(phi_I mu)_hat(k)| <= C min(r^delta,(1+|k|)^(-eta)).             (9)
```

Combine (8), (9), and the pointwise Fejer pairing justified above to get
rho_n(I)<=C[r^delta T^alpha+T^(alpha-eta)]. At T=r^(-delta/eta) this is
C r^u, u=delta(1-alpha/eta). In particular the positive exponent alpha
is paid for; it cannot be silently sent to zero at fixed L.

One explicit fixed denominator for the rational slice is

```
Cstar = C_mu C_nu 2^alpha/(1-2^(alpha-eta)),
Qstar = max(2, floor((2 Cstar)^(1/(eta-alpha)))+1),
kappa = 1/((M+2)Qstar^2).                                    (10)
```

Dyadic summation makes the Fourier tail past Qstar <1/2, so the grid average
of h_n exceeds 1/2. The same fixed-grid, positive-mass weak-limit argument
used for the full shift now gives (6). Its support lies in the nested
compatible symbolic image. Reflection by the selected rational translate
preserves dimension and gives BA(kappa) by the denominator calculation above.
Radix endpoints are rational and cannot belong to BA(kappa). No branchwise
deterioration of kappa occurs. Formula (10) is not a numerical certificate:
the external Fourier constants and sparsity modulus are not numerically fixed.

### The exact frozen ALA packet construction

Now b=10, A={1,...,9}. The frozen definition requires, for every sufficiently
large k and every u in A^k, an occurrence uc starting after an index
n in J_k={n:10^k+1<=n<10^(k+1)}. Let m=|P| and choose k0 so that
ell_k=(k+1)9^k<=10^k for every k>=k0 and 10^k0+2>m.
Force P and, for each k>=k0, the concatenation of all uc in lexicographic
order beginning at digit position 10^k+2. Its j-th occurrence has index
n_(k,j)=10^k+1+j(k+1), which lies in J_k. The packet ends at
10^k+1+ell_k<10^(k+1), so the packets are disjoint. At every intermediate
N in [10^k,10^(k+1)),

```
f(N)/N <= m/10^k + (9/8)(k+1)(9/10)^k -> 0.                  (11)
```

A compatible reference is P followed by 1s except at the packets. Every
packet digit is nonzero; the first following 1 resets P's terminal zero-run.
Every constrained stream has infinitely many markers c in {1,...,8}, so is
neither eventually 9 nor (by avoidance) eventually 0. Its coding is canonical
and lies in C_(0^L) intersect I(P) intersect ALA_(A,c).

Finally lambda>=b(1-b^(-L)), by substitution into its decreasing defining
sum, and (b/lambda)^L<2. Thus theta_(b,L)=O_b(log L/L)->0. Given s<1,
choose M with delta>s and set alpha=(eta/2)(1-s/delta). Choose L0(s) so
theta_(10,L)<alpha for every L>=L0(s). This choice is independent of c and P.
Apply (6) to (11): the dimension is at least (delta+s)/2>s, proving the
displayed restricted corollary. Removing the countable algebraic reals leaves
the same dimension and the same kappa. The parameter tuple
(m,w,A,c)=(L,0^L,{1,...,9},c) meets the existing P1 parameter class.

The [proper-SFT finite audit](../../../../workflows/experiments/p1prime_sft_fourier_audit_20260905.py)
was inspected and rerun locally: 12 small (b,L) models, 48 conditioning and
Fourier scenarios, sampled shifted-mask bounds, and long-packet tests passed.
Word sets and counts are enumerated exactly; probabilities and Fourier tests
use NumPy floating point. These remain `experiment`. The corrected analytic
argument and packet corollary were separately inspected; neither this audit
nor Pro's agreement upgrades them beyond `proof sketch`. No new manuscript
theorem, Lean assertion, novelty claim, or universal P1 resolution is made.
