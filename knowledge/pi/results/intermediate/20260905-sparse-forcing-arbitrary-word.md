# Sparse forcing while avoiding an arbitrary sufficiently long word

Status: proof sketch. Date: 2026-09-05.
The coordinator checked the argument below and reproduced the finite tests.
An independent Pro audit upheld it after the row-norm repair, including
the conditioning estimate, localization, fixed kappa and packet quantifiers.
The separate primary-precedent audit confirmed the analytic input and found
an older explicit decay estimate giving the length criterion below.
No Lean result, novelty claim, or statement about the digits of pi is made.

For every 0<s<1 there exists m0(s) such that every decimal word w of length
m>=m0(s), every digit d occurring in w, A={0,...,9}\{d}, every
c in A intersect {1,...,8}, and every finite prefix P avoiding w admit
kappa>0 with dim_H(C_w intersect I(P) intersect ALA_(A,c) intersect BA(kappa))>=s.

Here ALA is exactly the frozen definition in
[OPEN_PROBLEMS](../../workstreams/OPEN_PROBLEMS.md), including its windows
J_k={n:10^k+1<=n<10^(k+1)}. This gives restricted localized P1-PD/NE
instances, uniformly over all sufficiently long words. It does not establish
P1-FD for any fixed word or the universally quantified P1-PD/NE statements.
The quantifier is a threshold in word length, not a limit within one fixed
avoidance language.

## Exact block masks

Fix m>=2 and w=w_1...w_m. The prefix automaton has states 0,...,m-1,
recording the longest suffix which is a proper prefix p_u=w_1...w_u.
Completing w kills the path. Put B=10^m and let W_uv be the length-m
blocks surviving from u and finishing at v.

A forbidden occurrence ending at the r-th new digit, 1<=r<=m, is possible
exactly when m-r<=u and the suffix of p_u of length m-r equals p_(m-r).
It then prescribes the first r digits to be w_(m-r+1)...w_m.
For r=m this is the wholly internal occurrence, the block w itself.
The forbidden blocks from state u are therefore a union of at most m prefix
cylinders. Retain only inclusion-maximal cylinders; they are disjoint.
Call this family E_u.

After m new digits the terminal state depends only on the new block.
For state v, require suffix p_v and exclude longer prefix suffixes p_t,
v<t<m. Among the suffix cylinders contained in the p_v cylinder retain
only inclusion-maximal ones, a disjoint family T_v of size at most m-1-v.
With C^-(p) denoting a suffix cylinder, the exact indicator is

$$
1_{W_{uv}}=
(1-\sum_{E\in E_u}1_E)
(1_{C^-(p_v)}-\sum_{T\in T_v}1_T).
$$

This has at most (m+1)(m-v)<=(m+1)^2 signed terms. Each term is the
intersection of a prefix and suffix cylinder. Its integer block values
form an arithmetic progression of step 10^t, where t is the suffix
length, or an empty set or singleton if the prescriptions overlap.

Define the substochastic matrix K=K(0) by

$$
K_{uv}(t)=B^{-1}\sum_{z\in W_{uv}}e^{-2\pi i[z]_{10}t}.
$$

The shifted Dirichlet bound for an interval of N<=Q consecutive integers is

$$
\sup_t\sum_{\ell=0}^{Q-1}
\left|\sum_{j=A}^{A+N-1}e^{-2\pi i j(t+\ell/Q)}\right|
\le Q(2+\log Q).
$$

To see this, bound a summand by min(N,1/(2||t+ell/Q||)); sorting distances
to integers gives one term at most Q and the remaining harmonic sum.
For a progression of step 10^t the B-point grid reduces to a
10^(m-t)-point grid repeated 10^t times. Each normalized signed term
therefore costs at most 2+log B. Consequently

$$
\sup_t\max_u\sum_{\ell=0}^{B-1}\sum_v
|K_{uv}(t+\ell/B)|
\le L_m:=m(m+1)^2(2+m\log10).
\tag{1}
$$

## Two-block future comparison, uniformly over the word

One-block failure from any state lies in at most one prescribed-prefix
event of each length r=1,...,m. Hence K1>=sigma 1 with sigma=8/9.

For two blocks, condition the 2m independent digits on their last v digits
being p_v. There remain N=2m-v>=m+1 independent free digits. Four types
of bad event cover failure to survive from u and end exactly in state v:

- Occurrence crossing the initial boundary: probability <1/9, summing
  prescribed prefixes of lengths 1,...,m-1.
- Occurrence wholly in the free digits: probability <=(m+1)10^(-m).
- Occurrence crossing into the fixed suffix: probability <1/9, summing
  10^(-(m-t)) over 1<=t<=v.
- Terminal state t>v: probability <1/9, since a compatible longer prefix
  suffix prescribes t-v extra free digits.

No occurrence can be wholly within the fixed suffix, whose length is <m.
Each boundary event is either incompatible or has precisely the indicated
probability, regardless of overlap structure. The total bad probability is
at most 1/3+(m+1)10^(-m)<=1/3+3/100<1/2. Therefore

$$
\tfrac12\,10^{-v}\le (K^2)_{uv}\le 10^{-v}.
\tag{2}
$$

In particular, max_u(K^2H)_u/min_u(K^2H)_u<=2 for every nonzero H>=0.

## Sparse prescriptions and matrix Fourier induction

Let F be a fixed set of positive digit positions with
f(N)=|F intersect [1,N]|=o(N), and prescribe compatible digits on F.
Let nu_n=g_n dx be uniform independent digits conditioned through position
nm on avoidance and those prescriptions, followed by independent uniform
digits. Let H_j(u) be the probability of meeting all requirements in blocks
j,...,n from state u; H_(n+1)=1.

For z in W_uv, the exact conditioned block probability is

$$
Q_j(u,z,v)=
\chi_j(z)B^{-1}\frac{H_{j+1}(v)}{H_j(u)},
\tag{3}
$$

where chi_j imposes all current-block prescribed digits. A row with
H_j(u)=0 is set to zero. Rows on possible states sum to one.

If j,j+1,j+2 are clean, H_(j+1)=K^2 H_(j+3); (2) and K1>=sigma 1
give H_(j+1)(v)/H_j(u)<=2/sigma=9/4. At the horizon, one or two
final clean blocks give ratios at most sigma^-1 or sigma^-2, also <9/4.

Call j exceptional if it or either of its two successors meets F.
Among the first J blocks the exceptional count obeys
r_J<=3 f(m(J+2))=o(J), independently of n. Nonexceptional masks have
shifted row-l1 bound <=(9/4)L_m<=20m^4. Exceptional masks have the
trivial B bound. After the horizon use the uniform scalar block mask
times the identity; its bound 2+log B is also <=20m^4.

The correct induction quantity is the row norm

$$
\mathcal S_J=
\sum_{k=0}^{B^J-1}
\|e_0 M_1(k/B)\cdots M_J(k/B^J)\|_1.
$$

It is not the absolute value of that row times the all-ones column:
scalar cancellation need not survive a state-dependent continuation.
For any complex row z,

$$
\sum_{\ell=0}^{B-1}\|zM(t+\ell/B)\|_1
\le\sum_u |z_u|\sum_{\ell,v}|M_{uv}(t+\ell/B)|.
$$

Write k=k'+ell B^(J-1). Periodicity leaves the earlier factors unchanged.
Thus induction gives
S_J<=(20m^4)^(J-r_J) B^r_J<=B^(theta_m J+r_J), where

$$
\theta_m=\frac{\log(20m^4)}{m\log10}\longrightarrow0.
$$

Every remaining continuation column has sup norm <=1, so the row norm
bounds the full Fourier coefficient, including horizons beyond J.
For alpha>theta_m set
D_alpha=max(0,sup_J[r_J-(alpha-theta_m)J])<infinity.
Using a B-power frequency cutoff and symmetry gives

$$
\sup_n\sum_{|k|\le T}|\widehat\nu_n(k)|
\le C_\nu T^\alpha,\qquad
C_\nu=2B^{D_\alpha+\alpha},\quad T\ge1.
\tag{4}
$$

These constants are uniform over words of length m and compatible assigned
values on the fixed F. The block length is fixed before T tends to infinity.

## Rational slicing and the retained dimension loss

Use the rational-slicing argument and sharp localization established in
[the predecessor note](20260905-sparse-forcing-full-shift.md).
Its external input is the normalized delta_M-dimensional Hausdorff measure
mu on the bounded-partial-quotient set B_M, with interval bound C r^delta_M
and Fourier decay C(1+|k|)^(-eta_M), choosing 0<eta_M<delta_M.
The primary source is
[Jordan–Sahlsten, Corollary 1.4 and §6.7](https://arxiv.org/html/1312.3619);
equivalence of measures alone would not justify transferring Fourier decay.
Choose M with delta_M>max(s,1/2); these dimensions tend to one.

For theta_m<alpha<eta_M, (4) makes the Fourier pairing absolutely
summable with uniform tails. Fix an integer denominator Q large enough
that the nonzero Q-multiple Fourier sum has absolute value <1/2, for
every n. The Q-point grid average of mu*g_n is then >1/2. One fixed
numerator a works along an infinite subsequence.

The positive measures rho_n=g_n(a/Q-x)mu have uniformly bounded mass.
For a smooth interval bump phi_I, convolution with its rapidly decaying
Fourier coefficients gives

$$
|(\phi_I\mu)^{\wedge}(k)|
\le C\min(r^{\delta_M},(1+|k|)^{-\eta_M}).
$$

Pairing and splitting at T=r^(-delta_M/eta_M) yields the uniform bound

$$
\rho_n(I)\le C r^{\,\delta_M(1-\alpha/\eta_M)}.
\tag{5}
$$

Fejer pairing is valid at every grid point: for each fixed n the finitely
many step-function discontinuities have zero reflected mu-mass; bounded
Fejer means and absolute Fourier convergence justify the limit.
A nonzero weak limit is supported on B_M intersect
(a/Q minus the constrained symbolic image). Nested closed cylinders give
this support assertion without assuming their endpoints have unique coding.
Reflection modulo one is piecewise isometric and sends B_M into
BA(kappa) with the same fixed kappa=1/[(M+2)Q^2].
Thus the constrained symbolic image has BA(kappa) intersection of
dimension at least delta_M(1-alpha/eta_M).

## Exact timed packets, compatibility, and quantifiers

Fix w,d,A,c,P as in the statement. For all sufficiently large k, prescribe
all words uc, u in A^k, concatenated in lexicographic order beginning at
digit 10^k+2. Their packet length ell_k=(k+1)9^k is at most 10^k.
The j-th occurrence has index n=10^k+1+j(k+1), 0<=j<9^k;
hence n lies in J_k and the packet ends before position 10^(k+1).
Also prescribe P. Choose the initial packet index k0 sufficiently large
that the gap after P has at least m positions.

Choose beta in A intersect {1,...,8}, different from w's first and last
digits. Follow P with beta's and fill gaps between A-only packets with
beta's. A forbidden occurrence crossing out of P would end within the first
m-1 new positions and end in beta, contrary to beta!=w_m. After P all
digits lie in A, whereas w contains d. This is a compatible reference
sequence. A single beta is not claimed to reset every prefix state.

For N in [10^k,10^(k+1)), including N inside a packet,

$$
f(N)/N\le |P|/10^k+
\tfrac98(k+1)(9/10)^k\longrightarrow0.
$$

Every constrained sequence has infinitely many interior markers c, so is
neither eventually 0 nor eventually 9. Its coding is the unique canonical
decimal expansion, in C_w intersect I(P) intersect ALA_(A,c).

Given s, choose M as above and
alpha=(eta_M/2)(1-s/delta_M)>0. Choose m0(s)>=2 so that
theta_m<alpha for every m>=m0(s).
The threshold is independent of w,d,c,P. The exponent in (5) is then
(delta_M+s)/2>s. The denominator and positive kappa are fixed before
selecting a numerator or weak subsequence; kappa may depend on the chosen
packet set and prefix. Removing algebraic numbers, a countable set,
preserves this dimension and kappa.

## An explicit length criterion from an older analytic input

[Queffélec–Ramaré, Theorem 1.4](https://ramare-olivier.github.io/Maths/kaufmanbis.pdf)
constructs a probability measure on B_M with Frostman exponent t and Fourier
exponent h(t)-8 epsilon, where
h(t)=t(2t-1)/[(2t+1)(4-t)], for 1/2<t<dim_H B_M and epsilon>0.
This is a constructed measure, not necessarily Hausdorff measure.
Since h(t) tends to 1/9 as t increases to 1, the same slicing proves the
stated fixed-kappa conclusion for every 0<s<1-9 theta_m: choose
theta_m<alpha<(1-s)/9, then t close enough to 1, epsilon small enough,
and M with dim_H B_M>t. All choices precede rational slicing.

Thus 9 log(20m^4)<(1-s)m log10 is sufficient.
The parameter order and thresholds were independently audited in a further
mathematical review. The function theta_m decreases for m>=2. Exact integer comparisons
(20*81^4)^9<10^81 and (20*187^4)^18<10^187 give positive-dimensional
localized P1-PD/NE instances for every m>=81, and dimension strictly greater
than 1/2 for every m>=187. The bounds are not claimed optimal. They do not
certify a numerical kappa or settle the remaining lengths 1,...,80.

## Reproducible finite checks, not an infinite proof

With Python 3.10+ and NumPy available, from the PI root run:

    python3 workflows/experiments/p1prime_arbitrary_word_audit_20260905.py
    python3 workflows/experiments/p1prime_arbitrary_word_conditioning_20260905.py

The scripts print their results and write no files. Reproduction passed
10,320,000 exact entry-membership comparisons for all decimal words of
lengths 2 and 3 and eight length-4 words; 5,294 equality patterns through
length 8; and twenty longer words through length 64, including maximally
overlapping, unbordered, periodic, all-digit, and seeded random examples.
Eighteen prescribed-digit scenarios passed 384 conditional-row checks;
independent digit/block Fourier calculations differed by at most
1.25e-13. A coordinator-derived regression also exhibits the scalar-tail
gap concretely: avoid 01 for three length-2 blocks and prescribe the last
block to be 22. At frequency 50, truncating after the first block and
contracting against the all-ones column gives about 0.0001031, while the
full Fourier coefficient has magnitude about 0.0094428. The row-l1 bound
is about 0.1835893 and does bound it. These finite values illustrate why
the repaired induction is needed; its proof above is not numerical.
Shifted-grid samples are experiments, not certification of (1)
at every shift. The script also checks the two integer inequalities in the
explicit criterion. No numerical Fourier-decay multiplicative constant or
kappa is certified; the length thresholds follow from the analytic theorem.
