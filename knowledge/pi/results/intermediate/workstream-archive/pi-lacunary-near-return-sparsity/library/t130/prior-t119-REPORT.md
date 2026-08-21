# T119: collision concentration versus predictive and block-Hankel rank

Audit date: 2026-08-10 UTC.

Claim labels are load-bearing. Statements attributed to S1-S4 are
`literature-checked` against the four delivered primary PDFs and the exact
locators in `SOURCE_PINS.md`. Matrix translations, separators, transfer tests,
and comparisons in this report are `proof sketch` deductions. The bounded
replay in `verify_t119.py` is an `experiment`; it checks hashes, transcription,
and finite instances only.

This is a bounded cross-domain negative map. It establishes no property of the
prescribed constant, no canonical estimate, and no program conjecture.

```text
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 12
SEARCHED_DOMAIN_COUNT: 3
RETAINED_FINGERPRINT_COUNT: 3
RETAINED_FINGERPRINT_CAP: 4
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

## 1. Immutable statement and normalized scope

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

There is no original Erdos Problems URL. The file records a local formulation
dated 2026-07-22 and preserves its provenance. For integers `n,N>=1`, it fixes

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, the circle inequality
is strict, and the open quantifier order is

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
                         A*n*Q_pi(n,N)<=N^2.
```

The cutoff `N` may depend on `A,n`. Replacing the point, using exact word
equality, using aligned starts, prescribing `N`, taking infinitely many depths,
or proving an almost-everywhere/model theorem gives only a recorded sibling.

### Normalized agenda ambiguities

1. A **collision** below always counts ordered pairs and includes the diagonal.
2. A prefix cutoff restricts starts only. Blocks may inspect symbols beyond the
   cutoff, so parent and child rows use the same start mass.
3. A **prefix/suffix Hankel matrix** has word-concatenation entries `p(uv)`.
   It is not the sum-index matrix `(a_(i+j))` of a scalar sequence.
4. A **moment Toeplitz matrix** has entries `m_(a-b)`. Its sum-index Hankel
   counterpart is named separately.
5. Exact rank, numerical rank, nonnegative rank, automaton-state count, and
   support size are not interchangeable.
6. An approximation statement must specify the matrix, norm, threshold, and
   parameter ranges. Small determinant alone is not a numerical-rank bound.
7. Collision concentration means a lower bound for a fixed-depth squared
   frequency norm. It is not entropy, complexity, recurrence, or cancellation.
8. Finite computations can reject a proposed identity or threshold. They do
   not prove any universal or prescribed-point statement.

## 2. Common finite matrices and rank conventions

Let `Sigma` be a finite alphabet and let `x=x_0 x_1 ...` be an infinite word.
For `N>=1` and a finite word `w`, define the all-first-start frequency

```text
p_(x,N)(w) = (1/N) * #{0<=j<N : x_j ... x_(j+|w|-1)=w}.       (2.1)
```

For fixed prefix and suffix lengths `a,b>=0`, define

```text
H_(x,N)^(a,b)[u,v] = p_(x,N)(uv),
u in Sigma^a, v in Sigma^b.                                  (2.2)
```

Every entry uses the same `N` starts. If

```text
E_x(m,N)=sum_(w in Sigma^m) #{j<N:block_m(x,j)=w}^2,          (2.3)
```

then exactly

```text
||H_(x,N)^(a,b)||_F^2 = E_x(a+b,N)/N^2.                      (2.4)
```

Thus collision energy is the total squared singular-value mass of one fixed
split. It does not specify how that mass is distributed among singular values.

For a consistent process cylinder law `p`, define the finite all-word
truncation

```text
H_p^[L] = (p(uv))_(u,v in Sigma^(<=L)).                      (2.5)
```

Its direct limit is Fliess's infinite all-word Hankel matrix. For a scalar
sequence `c=(c_j)_(j>=0)`, define the distinct ordinary Hankel matrix

```text
A_n(c) = (c_(i+j))_(0<=i,j<n).                              (2.6)
```

For trigonometric moments `m_k`, define

```text
T_s(m) = (m_(a-b))_(0<=a,b<s).                              (2.7)
```

All exact ranks in this report are over `R` for real matrices and over `C` for
complex matrices. The norms are

```text
||M||_2 = sup_(||z||_2=1) ||Mz||_2,
||M||_F = (sum_(i,j)|M_ij|^2)^(1/2).                        (2.8)
```

For `tau>=0` and `*=2` or `F`, define the threshold rank

```text
rank_(*,tau)(M) = min{r>=0 : exists B, rank(B)<=r and
                                ||M-B||_* <= tau}.           (2.9)
```

At `tau=0`, this is ordinary algebraic rank. If `M` is invertible and
`||M-B||_2<sigma_min(M)`, then `B` is invertible: for a unit vector in
`ker B`, one would have `sigma_min(M)<=||M-B||_2`. Also, if `M` is `q x q`,

```text
sigma_min(M) >= |det M| / ||M||_2^(q-1).                   (2.10)
```

This follows because the determinant is the product of singular values and
the other `q-1` singular values are at most `||M||_2`. Equations (2.8)-(2.10)
fix every approximation convention used in the separators.

## 3. Source ledger and domain cap

The search used exactly three agenda domains and stopped after four primary
sources:

| ID | Domain | Source and exact locator | Role |
|---|---|---|---|
| S1 | symbolic entropy/collision | Fliess 1975, printed p. 4 Theorem 2.2; p. 16 Proposition 5.1 | C-PRED |
| S2 | Mahler/functional equations | Allouche-Peyriere-Wen-Wen 1998, printed pp. 2, 23-24, equation (31), Proposition 4.1, Corollary 4.1 | C-TM |
| S3 | arithmetic/fractal Fourier | Yang-Xie-Stoica 2016, printed pp. 3-4, equations (2)-(11), Theorem 1, Remark 1 | C-PRONY exact atomicity |
| S4 | arithmetic/fractal Fourier | Kunis-Peter-Romer-von der Ohe 2016, Definition 2.1, Theorems 3.1 and 3.7, Remark 3.4, equation (3.2) | C-PRONY ranges |

PDF URLs, DOI data, exact SHA-256 values, derivative hashes, and line anchors
are in `SOURCE_PINS.md`. The bounded query and stopping decisions are in
`SEARCH_LOG.md`.

## 4. C-PRED: finite predictive rank of a process

FINGERPRINT_CARD: C-PRED

### 4.1 Literature claim and complete range

S1 printed p. 4 defines, for a finite alphabet `X`, the all-word matrix

```text
H_r(f,g) = (r,fg),       f,g in X*.                         (4.1)
```

Its rank is `N` when it has a nonzero `N x N` minor and every
`(N+1) x (N+1)` minor vanishes. Theorem 2.2 assumes a field `K` and a formal
series `r in K<<X>>`. It states

```text
r is rational  <=>  rank H_r=N<infinity,                   (4.2)
```

and gives a dimension-`N` linear representation by matrices indexed by the
letters. Printed p. 16 defines a stochastic process to be rational when its
cylinder series is rational. Proposition 5.1 specializes (4.2): a process
`p:X*->[0,1]` is rational if and only if its Hankel rank is finite.

This is an exact characterization after finite rank is known. It does not say
that one high collision row forces finite rank, and it gives no approximation
threshold.

### 4.2 Exact concentration/full-rank separator

Use `Sigma={0,1}` and the consistent stationary block law

```text
mu = (1/2) delta_(0^infinity)
     +(1/2) integral_[0,1] Bernoulli(theta)^N dtheta.        (4.3)
```

This formula itself defines every finite cylinder probability. For every
`m>=1`,

```text
p_mu(0^m) = 1/2 + 1/[2(m+1)],
C_mu(m)   = sum_(w in Sigma^m) p_mu(w)^2 >= 1/4.            (4.4)
```

Hence collision concentration persists at every depth. Fix `L>=1` and in the
fixed split `H_mu^(L,L)` select rows and columns indexed by

```text
w_i=1^i 0^(L-i),       1<=i<=L.                            (4.5)
```

The zero atom contributes nothing. The resulting `L x L` matrix is

```text
G_L[i,j]
 = (1/2) integral_0^1 theta^(i+j)(1-theta)^(2L-i-j) dtheta
 = (1/2) (i+j)! (2L-i-j)! / (2L+1)!.                       (4.6)
```

It is the Gram matrix in `L^2[0,1]` of the linearly independent functions
`theta^i(1-theta)^(L-i)/sqrt(2)`. Therefore `det G_L>0` and

```text
rank H_mu^(L,L) >= L.                                      (4.7)
```

This gives unbounded exact rank while (4.4) remains bounded below. To make the
approximation threshold literal, note `||G_L||_2<=||G_L||_F<=L/2` and put

```text
tau_L = det(G_L)/(L/2)^(L-1) > 0.                          (4.8)
```

Equations (2.10) and (4.8) imply

```text
rank_(2,tau)(G_L)=L for every 0<=tau<tau_L.                 (4.9)
```

The threshold `tau_L` can decay rapidly; no uniform positive lower bound is
claimed. The separator refutes exact bounded rank and very-fine numerical
rank, not every coarser approximation notion.

SEPARATOR_C-PRED: For any proposed constant rank cap `R` derived only from the
persistent bound `C_mu(m)>=1/4`, take `L>R`. Equation (4.7) rejects the cap.
For a claimed spectral tolerance below `tau_L`, equation (4.9) is the
quantitative rejection test.

### 4.3 Attempted T7 implication and separate arithmetic premise

Let `a=floor(n/2)`, `b=n-a`, and let `R(kappa)` and `tau(kappa,N)` be declared
functions. A genuine inverse theorem of the needed shape would be

```text
INV-PRED:
E_pi(n,N)/N^2 >= kappa
  => rank_(2,tau(kappa,N))(H_(pi,N)^(a,b)) <= R(kappa).      (4.10)
```

Here `H_(pi,N)^(a,b)` means the literal decimal-block matrix (2.2) for the
decimal digit path of the prescribed orbit point, not a model process.

PI_SPECIFIC_PREMISE_C-PRED (conjectural, not asserted): for every `A>=1` and
all sufficiently large `n`, there is `N>=1` such that

```text
rank_(2,tau(1/(3*A*n),N))(H_(pi,N)^(a,b))
  > R(1/(3*A*n)).                                          (4.11)
```

If both (4.10) and (4.11) held, contraposition would give

```text
E_pi(n,N)/N^2 < 1/(3*A*n).
```

The checked T7 comparison `E_pi<=Q_pi<=3E_pi` would then give

```text
A*n*Q_pi(n,N) < N^2.                                      (4.12)
```

Thus the proposed T7 implication is displayed with its separately labeled
arithmetic premise. S1 supplies neither (4.10) nor (4.11), and (4.3)-(4.9)
refute (4.10) for fixed exact rank even at concentration `1/4`. If (4.11) were
replaced by a direct upper collision bound, factor-complexity growth, or the
conclusion (4.12), it would merely rename the existing T7 frontier. No such
replacement is accepted here.

Card result: rejected. Exact predictive rank is a characterization, not an
inverse consequence of collision concentration.

## 5. C-TM: ordinary coefficient Hankel rank in a Mahler system

FINGERPRINT_CARD: C-TM

### 5.1 Literature claim and complete range

Define the signed Thue-Morse sequence

```text
eta_0=1,       eta_(2j)=eta_j,       eta_(2j+1)=-eta_j.     (5.1)
```

Its generating series obeys the scalar two-Mahler equation

```text
F(z)=(1-z)F(z^2).                                          (5.2)
```

S2 printed p. 2 defines the shifted order-`n` coefficient matrix

```text
A_n^p(eta)=(eta_(p+i+j))_(0<=i,j<n),     p>=0,n>=1.        (5.3)
```

Printed p. 23 equation (31) records the signed/binary coding and Proposition
4.1 relates the corresponding determinants. Corollary 4.1 on printed p. 24
states, for the leading shift `p=0` and every `n>=1`,

```text
2^(1-n) det A_n^0(eta) = 1 (mod 2).                        (5.4)
```

Therefore

```text
det A_n^0(eta) != 0,       rank_R A_n^0(eta)=n.             (5.5)
```

The every-order statement is not silently extended to every positive shift;
S2 gives different ranges for shifted determinants.

### 5.2 Exact collision/full-rank separator

The finite prefix/suffix matrix attached to this card is not (5.3). For fixed
`K>r>=0`, put `L=2^r`, choose `a,b>=0` with `a+b=L`, and sample the
`Q=2^(K-r)` aligned length-`L` supertiles. Define

```text
B_TM(K,r;a,b)[u,v]
 = (1/Q) * #{0<=j<Q :
     prefix_a(block_L(mu^K(1),jL))=u and
     suffix_b(block_L(mu^K(1),jL))=v}.                     (5.5a)
```

This is a finite prefix/suffix matrix with the Frobenius and spectral norms
from (2.8), threshold rank (2.9), and declared approximation threshold
`tau=0`. It has at most two nonzero cells and therefore exact rank at most two.
It is deliberately aligned and is not the all-start target matrix (2.2); that
sampling failure is part of the rejection test, not hidden in notation.

Let `mu(1)=1,-1` and `mu(-1)=-1,1`. For integers `K>r>=0`, the word
`mu^K(1)` decomposes into `Q=2^(K-r)` aligned blocks of length `2^r`. They are
exactly `mu^r(1)` and `mu^r(-1)`. Since every substitution image contains one
of each sign, each block occurs `Q/2` times. Hence the ordered aligned
collision energy is

```text
E_al(K,r)=2*(Q/2)^2=Q^2/2.                                (5.6)
```

When the two cells are distinct, `||B_TM(K,r;a,b)||_F^2=1/2`. This elementary
`proof sketch` is replayed for all `1<=K<=8`; it does not use
the unverified T91 derivation as a premise. Equations (5.1)-(5.6) show that a
two-state automatic rule, one scalar Mahler equation, and persistent aligned
collision concentration coexist with maximal leading ordinary Hankel rank.

For an explicit numerical-rank threshold, every entry has modulus one, so
`||A_n^0||_2<=||A_n^0||_F=n`. Equation (5.4) gives
`|det A_n^0|>=2^(n-1)`. Therefore

```text
sigma_min(A_n^0) >= (2/n)^(n-1),
rank_(2,tau)(A_n^0)=n for 0<=tau<(2/n)^(n-1).              (5.7)
```

SEPARATOR_C-TM: the source matrix `A_n^0` has rank `n`, while the finite
prefix/suffix matrix `B_TM` has rank at most two solely because it discards all
nonaligned starts. Thus identifying the two rank notions is rejected exactly.
At any `n`, exact rank below `n` for the source matrix is rejected by (5.4).
At a claimed spectral tolerance below `(2/n)^(n-1)`, (5.7) rejects its
numerical rank below `n`. The threshold decays, so this does not reject coarse
approximate rank.

### 5.3 Attempted transfer and separate arithmetic premise

The matrix (5.3) reads a scalar coefficient sequence in unary index order. It
is not the decimal word-concatenation matrix (2.2), and (5.6) uses changing
aligned samples rather than one all-start row. Thus there is no sourced arrow
from (5.5) to either T7 or T107.

PI_SPECIFIC_PREMISE_C-TM (conjectural, not asserted): one would need an exact
prescribed-point coefficient sequence `c_j`, computable from the decimal orbit
without losing carries or starts, such that:

```text
(i) c has a source-valid finite Mahler/automatic representation;
(ii) high rank of A_n(c) forces high threshold rank of the all-start
     H_(pi,N)^(floor(n/2),ceil(n/2));
(iii) that high block rank implies the T7 upper energy bound in (4.12),
      or simultaneously implies both T107 row budgets.                    (5.8)
```

No source supplies any clause of (5.8) for the prescribed point. Clause (iii)
stated without an independent quantitative theorem is just T7 decay or T107.
Replacing it by superlinear factor-complexity growth only renames the accepted
factor-complexity frontier and does not give collision decay. Replacing the
bounded-entry determinant by a near-integer determinant of multiples of the
prescribed point recreates T114's rejected height/rank condition.

Card result: rejected. Automatic or Mahler low description does not imply low
ordinary Hankel rank, and ordinary rank has no all-start collision transfer.

## 6. C-PRONY: low PSD Toeplitz rank and atomic moments

FINGERPRINT_CARD: C-PRONY

### 6.1 Literal empirical moment matrix

For arbitrary circle points `y_0,...,y_(N-1)`, define

```text
m_k=(1/N) sum_(j=0)^(N-1) exp(2*pi*i*k*y_j),       k in Z,
T_s=(m_(a-b))_(0<=a,b<s).                                   (6.1)
```

Then `T_s` is Hermitian positive semidefinite and

```text
T_s=(1/N) V V*,       V[a,j]=exp(2*pi*i*a*y_j).              (6.2)
```

Repeated points can be combined into positive weights. For the actual orbit
one would set `y_j={10^j*pi}`, but no property of that specialization is
asserted.

### 6.2 Literature claims and all ranges

S3 printed p. 3 equations (2)-(8) and printed p. 4 equations (9)-(10) define
`d`-level Toeplitz matrices and the normalized Vandermonde columns. Theorem 1,
printed p. 4, assumes

```text
d>=1, T is PSD d-level Toeplitz of size (n_1,...,n_d),
rank T=r<min_j n_j.                                         (6.3)
```

It concludes the unique representation

```text
T=sum_(h=1)^r p_h a(f_h)a(f_h)*,
p_h>0, f_h distinct in the d-torus.                         (6.4)
```

Remark 1 states that the strict cutoff in (6.3) is tight. PSD, Toeplitz
structure, and the rank cutoff are all load-bearing.

S4 Definition 2.1 assumes `M` pairwise distinct parameters
`z_j in C_*^d=(C\{0})^d`, so every coordinate is nonzero, and nonzero complex
weights in an `M`-sparse exponential sum. For degree `n`, it defines

```text
I_n={0,...,n}^d,
T_n(f)=(f(k-l))_(k,l in I_n).                               (6.5)
```

Theorem 3.1 assumes `n>=M` and identifies the node set with the zero set of
the kernel; the necessity of this universal degree range is also stated.
Remark 3.4 gives the sum-index Hankel variant

```text
J_n={k in N_0^d:||k||_1<=n},
H_n(f)=(f(k+l))_(k,l in J_n).                               (6.6)
```

The same `n>=M` range remains, arbitrary parameters in `C^d` are then allowed
including zero coordinates, and the variant uses `binom(2n+d,d)` samples.

For positive weights at `q`-separated torus nodes, S4 Theorem 3.7 assumes

```text
n>=2d/q.                                                     (6.7)
```

With its positive diagonal preconditioner `W`, it gives

```text
cond_2(W T_n W)
 <= [((nq)^(d+1)+(2d)^(d+1))/((nq)^(d+1)-(2d)^(d+1))]
    * (max_h p_h/min_h p_h).                                (6.8)
```

Here `cond_2(X)=||X||_2 ||X^dagger||_2`, using the Moore-Penrose
pseudoinverse, because the moment matrix is generally rank deficient.

Equation (3.2) combines (6.7) with `n>=M`. These theorems recover an already
atomic moment model; they do not infer atomicity from decimal clustering.

### 6.3 Exact clustering/full-rank separator

Fix `r>=2`, a decimal depth `L>=1`, and an integer `s>=1` with `r<=10^s`.
Put

```text
delta=10^(-(L+s)),       t_j=j*delta,       0<=j<r,
mu_(r,L)=(1/r) sum_(j=0)^(r-1) delta_(t_j).                (6.9)
```

All points lie strictly in the same depth-`L` decimal cylinder because
`0<=t_j<10^(-L)`. Its ordered cylinder-collision energy is the maximal `r^2`,
and every ordered pair has circle distance below `10^(-L)`.

The candidate-specific finite prefix/suffix matrix is defined directly from
the nonterminating-zero decimal expansions of the sampled points. For
`a,b>=0`, `a+b=L`, put

```text
B_cyl^(a,b)[u,v]
 = (1/r) * #{0<=j<r : the first L decimal digits of t_j equal uv}. (6.9a)
```

All points in (6.9) have first `L` digits `0^L`, so `B_cyl` has one entry
equal to one and all others zero. Hence, with the norms (2.8) and threshold
rank (2.9),

```text
||B_cyl||_2=||B_cyl||_F=1,
rank_(2,tau)(B_cyl)=rank_(F,tau)(B_cyl)=1 for 0<=tau<1,
rank_(*,tau)(B_cyl)=0 for tau>=1.                           (6.9b)
```

For an actual orbit prefix, the same definition uses the first `L` digits of
`{10^j*pi}` for `0<=j<N`; it is exactly the fixed split (2.2). No property of
that specialization is asserted.

Let `m_k` be the moments of (6.9) and use the `(r+1)x(r+1)` matrix
`T_(r+1)` from (6.1). The first `r` rows of its Vandermonde factor are square,
with determinant

```text
product_(0<=a<b<r)
  (exp(2*pi*i*t_b)-exp(2*pi*i*t_a)) != 0.                  (6.10)
```

Thus

```text
rank_C T_(r+1)=r.                                          (6.11)
```

S3 applies because `r<r+1` and returns the same `r` distinct atoms. Therefore
maximal decimal clustering at a finite scale does not collapse exact moment
rank.

For a quantitative two-phase test, take `r=2`,
`delta=10^(-(L+1))`, and the `3x3` matrix. Its two nonzero eigenvalues are

```text
lambda_1=2+cos(2*pi*delta),
lambda_2=1-cos(2*pi*delta)=2*sin(pi*delta)^2.               (6.12)
```

Consequently

```text
rank_(2,tau)(T_3)=rank_(F,tau)(T_3)=2
for 0<=tau<2*sin(pi*delta)^2.                               (6.13)
```

At or above that threshold, the matrix can appear rank one although its exact
rank remains two. S4 defines `q`-separation by the strict inequality
`sep>q`. Points of exact separation `delta` therefore require `q<delta`.
The first integer degree at which the displayed finite condition-number bound
can be invoked satisfies

```text
n>=2*10^(L+1)+1.                                           (6.14)
```

At the excluded equality endpoint the denominator in (6.8) vanishes. The
valid degree is exponentially larger than the decimal depth. This is a
quantitative resolution cost, not a theorem about orbit length.

SEPARATOR_C-PRONY: the same finite sample has prefix/suffix rank one below
threshold one by (6.9b), but exact moment rank `r` by (6.11); direct rank
identification is therefore false. Choose any proposed exact moment-rank cap
`R`, set `r>R`, and use (6.9)-(6.11). For numerical moment rank one in the
two-phase case, use the exact threshold (6.13). For a claimed source-conditioned
recovery at degree below `2*10^(L+1)+1`, use (6.14).

### 6.4 Attempted T107 implication and separate arithmetic premise

Atomicity is predictive structure, not Fourier decay. A finite atomic measure
can have coherent nondecaying coefficients; the clustered measure (6.9) is the
opposite of anti-concentration at depth `L`.

PI_SPECIFIC_PREMISE_C-PRONY (conjectural, not asserted): to reach T107 one
would need one strictly increasing positive prefix sequence `N(k)`, a weak
limit, and for every `k>=k0` and `m0<=m<=k` enough levels `1<=ell<m` such that
the moment-rank certificate separately implies

```text
active successor boundary load + (1/2) active parent load
  <= N(k)/(40*10^ell),
||rowFourierRemainder(ell,N(k))||
  <= N(k)^2/(10*10^ell),                                   (6.15)
```

with averaged defect at most `card-(d*m-B)`. Under (6.15), the checked T107
theorem gives at least `d*m-B` literal T64-good levels and hence its displayed
conditional small-ball consequence.

S3-S4 supply neither boundary control nor Fourier smallness. Treating (6.15)
as an assumption merely restates T107. Replacing Vandermonde nonvanishing by
an arithmetic lower bound for near-integer multiples recreates T114's rejected
determinant-height condition. There is also no T7 implication: (6.9) has
maximal collision while its exact rank is arbitrary.

Card result: rejected. Prony theory characterizes an already sparse spectrum;
decimal clustering does not produce sparse spectral support.

## 7. Mandatory fingerprint comparison ledger

Verification levels are part of the comparison. Reports under `notes/` are
unverified exploration and are not used as discharged premises. T109 is read
from its content-addressed proof-ledger blob. The completed T117 and T118
reports are now inspectable at the exact comparison pins below. Their source
statements retain the reports' `literature-checked` labels, while their new
deductions remain `proof sketch`; neither report is used as a discharged
premise here.

| Prior | C-PRED comparison | C-TM comparison | C-PRONY comparison |
|---|---|---|---|
| T91 | The T91 note argues (unverified) from aligned/canonical samples; C-PRED uses one all-start fixed-mass matrix and shows concentration still permits unbounded rank | Same Thue-Morse system, but T91's object is aligned equal-block energy while C-TM is the sum-index coefficient matrix; (5.6) is re-derived here | No substitution or representative sample; C-PRONY uses circle moments and preserves every atom |
| T94 | The T94 note's finite paperfolding state closure counts equality; Fliess rank is global word-concatenation dimension, and the separator is not paperfolding | Ordinary coefficient rank is not T94's 192-state carry/profile recurrence; no scalar recurrence is inferred | Prony nodes are frequencies, not paperfolding carry states; no multiplicity is discarded |
| T97 | The T97 note argues a dyadic diagonal collision formula; C-PRED is a general process rank obstruction at every depth | No paperfolding diagonal asymptotic; APWW gives every-order determinant nonvanishing | No dyadic collision asymptotic; exact atomic rank can grow inside one cylinder |
| T101 | The T101 note argues finite-state paperfolding has only `O(1/n)` splitting mass; C-PRED independently shows finite collision information does not control predictive rank | Confirms a different warning: two-state description can coexist with full ordinary rank, but supplies no successor splitting | Atomic rank supplies neither adjacent energy decrement nor positive-density splitting |
| T103 | T103's source-pinned Toeplitz point uses periodic holes and collision lower bounds; C-PRED has no tower and tests rank directly | No Toeplitz dynamical tower or hole density; `Toeplitz matrix` is not involved in C-TM | The word Toeplitz in C-PRONY means constant diagonals of a moment matrix, not a Toeplitz subshift or periodic-hole tower |
| T104 | No ambient measure Fourier decay or fixed-fiber averaging; C-PRED is an exact process-law algebraic test | No radial Mahler asymptotic or ambient Fourier decay; the bounded sequence determinant is different | S3-S4 infer atomicity from rank, not decay from an ambient fractal measure; named-point and Fourier gaps remain explicit |
| T105 | Word-concatenation rank is not additive energy/BSG of `D_N` and evaluates no prescribed character | Coefficient Hankel rank is not additive energy or a modular geometric sum | Moment rank is not additive energy of `D_N`; sparse atoms do not bound T105's adaptive character |
| T109 | T109 transports model block laws through TV; C-PRED infers nothing through perturbation and its separator is intrinsic | No Markov perturbation, shadowing, or Wasserstein transfer | No robustness transport; S3-S4 start from exact moments, and the kill is only a certificate-applicability test |
| T111 | T111 constructs a collision-avoiding odd de Bruijn sibling; C-PRED starts from concentration and rejects bounded rank | No de Bruijn selector or remote label separation | Clustered atoms are the opposite of T111 separation and do not construct a sibling decimal |
| T114 | Nearest overlap: C-PRED uses probability Gram minors with bounded entries, not near-integer determinants paying height `10^N`; no T114 lower bound is imported | APWW determinants have `+-1` entries and test one automatic sequence, not multiples of the prescribed point; transferring them would recreate T114 | Vandermonde nonvanishing is algebraic; close phases make determinants tiny, so it does not reverse T114's height sign |
| T115 | No Riesz coefficient recursion or persistent Fourier ray; predictive Hankel rank is a different object | Same substitution/Mahler ancestry, but APWW coefficient rank is not T115's finite Riesz recursion | Atomic moment recurrences can also retain coherent rays; they do not supply T115's missing cancellation or T107 boundary estimate |
| T116 | No effective avoidance game or constructed safe branch; the process separator is a law-level obstruction | No computable avoidance sibling; automaticity alone is tested and rejected as a low-rank inference | The clustered finite measure is a rank separator, not a selected avoiding point or diagonal-only orbit |
| T117 | T117's Legendre model uses squarefree shifted subset products and pointwise character cancellation to derive low equal-block collision on finite periods; C-PRED instead asks whether high collision forces low all-word predictive rank, and its separator shows it does not | Both use structured binary words, but T117 has finite-field pattern cancellation and no Mahler/automatic coefficient representation; C-TM has aligned high collision and maximal sum-index coefficient Hankel rank, so neither rank nor sampling notion transfers | T117 bounds every finite-field word count by character sums; it has no PSD Toeplitz moment matrix, atomic-support hypothesis, node separation, or Prony rank conclusion |
| T118 | T118 fixes an exact-order private prime-power modular orbit and tests short exponential-sum cancellation; it supplies no process cylinder law, rational series, or finite predictive-rank inference from collision | T118's prescribed nearest numerator gives modular phases with no automatic/Mahler coefficient recurrence and no sum-index determinant theorem; its logarithmic-length applicability failures are disjoint from C-TM's ordinary Hankel-rank separator | A finite modular orbit is atomic as a measure, but T118 seeks pointwise cancellation for its prescribed numerator and does not infer sparse support from decimal clustering; exact multiplicative order supplies neither Prony separation nor low moment rank |

Exact comparator hashes used for this table are:

```text
T91  a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e
T94  f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10
T97  fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e
T101 ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e
T103 ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0
T104 2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5
T105 ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f
T109 6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf
T111 89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8
T114 db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca
T115 29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36
T116 573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1
T117 ee6974209f7e6064f30ec3ae83240cb1e7994e66566e920417dbf361da0ff30b
T118 2ed7a176bedb2f3a1627dffd4002f6b6141f078fe5c73798041b4fba90c7410e
```

T91, T94, T97, and T101 are unverified notes. T103-T105, T109, T111, and
T114-T118 have literature-checked source components and proof-sketch
deductions as recorded in their reports. T117 is a finite-field low-collision
model; T118 is a private-prime-power modular applicability audit. None of
these proof sketches is used as a premise in Sections 4-6.

## 8. Exact rejection ledger

| Card | Matrix and rank notion | Collision input | Exact or quantitative test | First fatal transfer gap |
|---|---|---|---|---|
| C-PRED | fixed-split `H^(L,L)`; `rank_(2,tau)` | `C_mu(m)>=1/4` for every `m` | `det G_L>0`; reject rank `<L` for `tau<tau_L` | Fliess characterizes finite rank but does not infer it from one collision row |
| C-TM | finite prefix/suffix `B_TM` at `tau=0`, compared with `A_n=(eta_(i+j))` and `rank_(2,tau)` | aligned `E_al/Q^2=1/2` at every supertile scale | `rank B_TM<=2` only after downsampling while normalized `det A_n` is odd; reject source rank `<n` below `(2/n)^(n-1)` | ordinary unary-index rank and aligned samples do not control all-start decimal energy |
| C-PRONY | finite prefix/suffix `B_cyl` plus PSD Toeplitz `T_(r+1)`; exact and threshold rank in spectral/Frobenius norm | all `r` points in one depth-`L` cylinder, collision `r^2` | `rank B_cyl=1` below `tau=1` but moment rank is `r`; two-node threshold `2 sin^2(pi delta)`; stable source resolution `n>=2/delta+1` at this integer reciprocal scale | atomicity gives no boundary budget or Fourier cancellation |

The three tests isolate three distinct failures:

1. fixed-depth squared frequency mass does not bound exact predictive rank;
2. automatic/Mahler low description does not bound ordinary coefficient
   Hankel rank and aligned collisions do not repair the sample mismatch;
3. metric clustering does not merge distinct Fourier atoms, while resolving
   close atoms costs inverse separation.

No card yields a surviving transfer. The only displayed T7 route, (4.10)-
(4.12), lacks its inverse theorem and its separate arithmetic premise. The
only displayed T107 route, (6.15), is exactly the analytic premise the source
does not supply. No pi-specific premise is silently counted as established.

## 9. Replay and review boundary

From a directory containing only the delivered artifacts, run

```text
python3 verify_t119.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes, source anchors, caps,
the complete comparator list, the single endpoint marker, and the three
separately labeled pi-specific premises. With exact rational arithmetic it
checks the C-PRED Gram determinants and bounded Thue-Morse determinants and
aligned collisions. Floating-point checks only validate finite instances of
the Prony Vandermonde and two-phase formulas; their universal justification is
the displayed proof sketch and pinned source theorem, not the experiment.

SCOPED_VERDICT: close

This closes only the three audited source applications as routes from

```text
persistent empirical block-collision concentration
  => quantitatively low predictive, ordinary Hankel, or moment rank.
```

The source theorems characterize or recover rank after extra rational-series,
functional, PSD Toeplitz, atomic-support, or separation hypotheses are already
present. The separators show that the audited collision data alone supply none
of those hypotheses. This does not rule out a different theorem using stronger
deterministic all-start structure. Reopening this fingerprint would require a
theorem that derives a declared singular-value tail from the actual all-start
block matrix and independently converts that tail into T7 decay or both T107
row budgets, without invoking factor-complexity growth or T114's
determinant-height condition. No bounded successor is selected.
