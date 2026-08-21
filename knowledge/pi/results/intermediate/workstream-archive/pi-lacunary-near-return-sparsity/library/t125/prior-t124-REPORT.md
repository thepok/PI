# T124: arithmetic monodromy on decimal congruence quotients

Status: `proof sketch`. The quoted source statements are `literature-checked`
against the eight pinned primary PDFs. The deductions and comparisons in this
note are not machine-checked. The replay is an `experiment` checking only the
displayed finite algebra.

Search date: 2026-08-10 UTC.

`PRIMARY_SOURCE_COUNT: 8`

`RETAINED_CANDIDATE_COUNT: 3`

## 1. Provenance and normalized target

Original source URL: none. The canonical question was formulated by this
program and is preserved byte-for-byte as `canonical_statement.txt`, SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.

For real `x`, let

\[
 \|x\|_{\mathbb R/\mathbb Z}=\inf_{a\in\mathbb Z}|x-a|.
\]

For integers `n,N >= 1`, the canonical statistic is

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\]

Pairs are ordered and the diagonal is included. The quantifier order is
`for every A >= 1, eventually for every n, there exists N >= 1`, with `N`
allowed to depend on `A,n`. T124 does not alter that statement. All models
below replace the point, orbit, or coding and are therefore sibling models.

### Ambiguities fixed before the search

1. "Arithmetic monodromy" means an explicitly generated integral monodromy
   group together with its reductions modulo a stated family `q`.
2. "Orbit mixing" may concern a branching word walk. It is not silently
   identified with one deterministic coefficient orbit.
3. "Decimal-compatible" means a theorem applicable to the growing family
   `q_m=10^m`, not merely to squarefree `10` or to moduli coprime to `10`.
4. A Fourier estimate for signed linear phases is not treated as an estimate
   for an unweighted lacunary phase.
5. A theorem about a stationary or random walk is a related-model result until
   a pointwise coding identifies the prescribed deterministic orbit.

## 2. Caps and search lanes

The search inspected exactly eight primary papers, below the cap of twelve,
and retained exactly three named systems, below the cap of four. The four
searched lanes were:

1. Mahler/functional-equation systems: S5, S6.
2. Arithmetic and fractal Fourier decay: S3, S8.
3. Symbolic entropy/collision theory: S6, S7.
4. Arithmetic monodromy and short structured exponential sums: S1, S2, S4.

`SEARCH_LOG.md` records the bounded decisions. `SOURCE_PINS.md` gives URLs,
hashes, and exact locators. No source outside S1--S8 is used for a new
literature claim.

## 3. Checked interfaces used only as targets

These statements are machine-checked in the supplied library. They do not
provide a transfer from any candidate below.

### 3.1 T7 collision shape

The checked T7 file defines ordered, diagonal-inclusive decimal cylinder
energy `E_pi(n,N)` and has

\[
 E_\pi(n,N)\le Q_\pi(n,N)\le3E_\pi(n,N).
\]

Its exact finite frontier is

\[
 \forall A\ge1\ \exists n_0\ge1\ \forall n\ge n_0\ \exists N\ge1:
 A n E_\pi(n,N)\le N^2.
\]

Locator: `FiniteCylinderEnergy.lean`, SHA-256
`cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c`,
lines 292--318 and 346--386.

### 3.2 T10 Fourier obstruction shape

The checked T10 conclusion forced by failure of its canonical input contains,
for arbitrarily requested `K`, a length `J=N-r >= K`, `1 <= h <= 256 A n`,
and

\[
 \left|\sum_{j=0}^{J-1}
 e\bigl(h(10^r-1)10^j\pi\bigr)\right|
 > {J\over131072 A^2n^2}.
\]

Locator: `LongLagResonance.lean`, SHA-256
`63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947`,
lines 829--894.

### 3.3 T107 row budgets

The checked T107 interface has literal levels `1 <= ell < m`, boundary budget

\[
 {P\over40\,10^\ell},
\]

and collected-Fourier budget

\[
 {P^2\over10\,10^\ell}.
\]

It requires one strictly increasing positive prefix family and every triangular
row in the displayed range. Locator: `T107AveragedTriangularFejer.lean`,
SHA-256
`45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`,
lines 31--69 and 150--199.

## 4. Common branching-walk collision calculation

This elementary calculation is used for H1 and as a failed substitution for
H2. It is reproduced here rather than attributed to a prior note.

Let `G_q` be a finite group, let `S` be a symmetric generating multiset, and
make its walk lazy. Suppose its Markov operator has

\[
 \|p_L-u_q\|_2\le \rho^L\|\delta_1-u_q\|_2\le\rho^L,
 \qquad 0<\rho<1,                                      \tag{4.1}
\]

where `p_L` is the endpoint law after `L` steps and `u_q` is uniform. Suppose
also that a label `lambda_q:G_q -> Z/qZ` has exactly `R_q` points in each
fiber. Realize the lazy walk by a uniform alphabet of size `B`, let
`N=B^L`, and let `A_z` count words whose endpoint label is `z`. Then

\[
 C(q,L):=\sum_{z\bmod q}A_z^2                         \tag{4.2}
\]

counts ordered pairs of words with equal labels, including all diagonal
pairs. Write the projected law as `q^{-1}+Delta_z`. Fiberwise
Cauchy--Schwarz and (4.1) give

\[
 \sum_z\Delta_z^2
 \le R_q\sum_{g\in G_q}(p_L(g)-u_q(g))^2
 \le R_q\rho^{2L}.
\]

Consequently

\[
 \boxed{C(q,L)\le N^2(q^{-1}+R_q\rho^{2L}).}          \tag{4.3}
\]

For `q=10^m`, fixed `A>=1`, and any `m` satisfying

\[
 A m10^{-m}\le\tfrac12,                               \tag{4.4}
\]

the choice

\[
 L\ge {\log(2AmR_{10^m})\over-2\log\rho}             \tag{4.5}
\]

implies the exact T7-shaped related-model inequality

\[
 A m C(10^m,L)\le N^2.                                \tag{4.6}
\]

This is not an application of T7 because the labels are monodromy labels, not
decimal cylinders of the canonical orbit.

## 5. Candidate H1: rank-two Gauss hypergeometric monodromy

### 5.1 Exact recurrence

Define `theta=z d/dz` and

\[
 \mathcal L_2=\theta^2-z(\theta+\tfrac16)(\theta+\tfrac56).
\]

Its holomorphic solution at zero is

\[
 F_2(z)={}_2F_1(\tfrac16,\tfrac56;1;z)
       =\sum_{n\ge0}a_nz^n,
\]

where the complete recurrence and parameter range are

\[
 a_0=1,\qquad
 36n^2a_n=(6n-5)(6n-1)a_{n-1}\quad(n\ge1).            \tag{H1.1}
\]

### 5.2 Congruence representation, modulus, and orbit

S1 defines the monodromy of a hypergeometric operator from companion
matrices. For

\[
 f=X^2-X+1,\qquad g=(X-1)^2,
\]

the matrices are

\[
 A=\begin{pmatrix}0&-1\\1&1\end{pmatrix},\qquad
 B=\begin{pmatrix}0&-1\\1&2\end{pmatrix}.             \tag{H1.2}
\]

They are integral with determinant one. Moreover

\[
 A^{-1}B=\begin{pmatrix}1&1\\0&1\end{pmatrix}=T,
 \qquad AT^{-1}=\begin{pmatrix}0&-1\\1&0\end{pmatrix}=S,
\]

so `Gamma=<A,B>=SL_2(Z)` by the standard generators `S,T`. For every
`m>=1`, set

\[
 q_m=10^m,\qquad G_m=SL_2(\mathbb Z/q_m\mathbb Z),
\]

and reduce (H1.2) entrywise. The orbit used here is not the coefficient orbit:
it is the branching multiset of endpoints of words of length `L` in the
eight-symbol lazy alphabet consisting of four identity symbols and one copy
of each of `A,A^{-1},B,B^{-1}`. It starts at the identity. Thus `N=8^L`.

The exact group and balanced-fiber sizes are

\[
 |G_m|=72\,10^{3m-2},\qquad
 R_m={|G_m|\over10^m}=72\,10^{2m-2}.                  \tag{H1.3}
\]

A balanced label exists set-theoretically because `10^m` divides `|G_m|`.
No arithmetic significance is assigned to an arbitrary such label.

### 5.3 Source theorem and quantifiers

S1, arXiv pages 1--4, defines the operator, companion matrices, and monodromy
and states that its arithmeticity criterion also holds in dimension two.
The equality with `SL_2(Z)` above is a direct matrix calculation, not a quote.

S3, Theorem 1 on arXiv pages 1--2, states: for every fixed finite symmetric
`S subset SL_d(Z)` generating a Zariski-dense subgroup `G`, the Cayley graphs
of `pi_q(G)` with generators `pi_q(S)` form an expander family as `q` ranges
over all positive integers. It also gives a fixed `q_0` for surjectivity when
`gcd(q,q_0)=1`. Here surjectivity for every `q` follows independently from
`Gamma=SL_2(Z)`.

The expander conclusion and the lazy modification yield a constant
`rho in (0,1)`, depending only on the fixed generators and not on `m`, for
(4.1). This spectral conversion is an elementary expander consequence, not a
separate quantitative constant quoted from S3.

### 5.4 Displayed T7 substitution

Insert (H1.3) into (4.3):

\[
 C_m(L)\le8^{2L}
 \left(10^{-m}+72\,10^{2m-2}\rho^{2L}\right).         \tag{H1.4}
\]

For (4.4) and

\[
 L\ge {\log(144Am\,10^{2m-2})\over-2\log\rho},       \tag{H1.5}
\]

one obtains

\[
 Am C_m(L)\le8^{2L}.                                  \tag{H1.6}
\]

Thus arithmetic congruence expansion really does supply logarithmic-depth
collision control for this branching related model on every decimal modulus.

### 5.5 Cheap kill test

**Kill H1 for transfer:** the recurrence (H1.1) has one deterministic index
path, while (H1.4) averages all `8^L` monodromy words. Neither S1 nor S3 gives
a map from coefficient index, decimal multiplication, or carries to those
words. An arbitrary balanced label is not the decimal-cylinder map. Therefore
the first missing equality is

\[
 \left\lfloor10^m\{10^j x\}\right\rfloor
 \stackrel{?}{=}
 \lambda_m(\gamma(w_j)),                              \tag{H1.7}
\]

for one prescribed point `x` and a collision-preserving family of words
`w_j`. No such equality is sourced or derived. Expansion is therefore a real
related-model mechanism but not a deterministic-orbit estimate.

## 6. Candidate H2: rank-four arithmetic symplectic hypergeometric group

### 6.1 Exact recurrence

Use the standard hypergeometric orientation

\[
 \mathcal L_4=\theta^4-z(\theta+\tfrac16)^2
                         (\theta+\tfrac56)^2.
\]

The holomorphic solution

\[
 F_4(z)={}_4F_3(\tfrac16,\tfrac16,\tfrac56,\tfrac56;1,1,1;z)
       =\sum_{n\ge0}b_nz^n
\]

has the complete recurrence

\[
 b_0=1,\qquad
 6^4n^4b_n=(6n-5)^2(6n-1)^2b_{n-1}\quad(n\ge1).       \tag{H2.1}
\]

Interchanging the two source polynomials reverses the standard
hypergeometric orientation but does not change the generated group.

### 6.2 Congruence representation, modulus, and orbit

S1 specializes

\[
 f=(X-1)^4,\qquad g=(X^2-X+1)^2
\]

and their companion matrices

\[
 A=\begin{pmatrix}
 0&0&0&-1\\1&0&0&4\\0&1&0&-6\\0&0&1&4
 \end{pmatrix},\quad
 B=\begin{pmatrix}
 0&0&0&-1\\1&0&0&2\\0&1&0&-3\\0&0&1&2
 \end{pmatrix}.                                      \tag{H2.2}
\]

The local monodromy transvection is

\[
 C=A^{-1}B=
 \begin{pmatrix}
 1&0&0&-2\\0&1&0&3\\0&0&1&-2\\0&0&0&1
 \end{pmatrix}.                                      \tag{H2.3}
\]

Define the rank-four group freshly by

\[
 \Gamma_4=\langle A,B\rangle\subset Sp_4(\mathbb Z).
\]

For every positive integer `q`, reduction of the integral matrices defines

\[
 \Gamma_4(q)=\ker(\Gamma_4\to GL_4(\mathbb Z/q\mathbb Z)),
 \qquad G_{4,q}=\Gamma_4/\Gamma_4(q).                 \tag{H2.4}
\]

The contemplated orbit is the lazy branching word orbit from the identity in
`G_{4,q}` under `A,A^{-1},B,B^{-1}`. Again, it is not the sequence of coefficients
in (H2.1).

### 6.3 Source theorems and quantifiers

S1, Corollary 1.3 on printed page 596 (arXiv page 6), states that this
`Gamma_4 subset Sp_4(Z)` is arithmetic, hence finite index. Its proof identifies
`f-g=-2X^3+3X^2-2X` and invokes Theorem 1.1; see arXiv page 15.

S2, Theorem 1 on arXiv pages 1--2, states that for a fixed finitely generated
`Gamma subset GL_d(Z[1/q_0])`, its congruence Cayley graphs are expanders as
`q` ranges over squarefree integers coprime to `q_0` exactly when the connected
component of the Zariski closure is perfect. Here the connected closure is the
perfect group `Sp_4`. Because (H2.2) is integral, its reduction is defined with
denominator modulus `q_0=1`; S2 therefore supplies expansion for every
squarefree `q`.

S3 does not replace S2 here: S3 assumes Zariski density in `SL_d`, whereas this
group has the proper Zariski closure `Sp_4` inside `SL_4`.

### 6.4 First failed inspected T7 substitution

Counterfactually, a uniform `rho<1` on `q_m=10^m` and a balanced label would
give exactly (4.3)--(4.6). The first theorem hypothesis already fails:

\[
 10^m\text{ is squarefree}\quad\Longleftrightarrow\quad m=1.             \tag{H2.5}
\]

Replacing `10^m` by its radical gives the fixed modulus `10`; then the uniform
term in (4.3) is `1/10`, so

\[
 Am\,q^{-1}=Am/10>1/2\qquad\text{whenever }m>5/A.       \tag{H2.6}
\]

Thus S2's squarefree theorem has no growing decimal-compatible subfamily and
cannot meet even the uniform term of the T7-shaped budget. Arithmeticity
leaves open in this bounded audit a different property-(T) route to expansion
on all finite quotients. No primary property-(T) source was inspected, so this
note neither uses that route nor rejects H2 on spectral grounds.

### 6.5 Cheap kill test

**Kill H2 for the inspected substitution and transfer:** S2's decimal
prime-power incompatibility occurs before its spectral gap can be substituted.
Even if an all-quotient gap is supplied by another theorem, the resulting
estimate is still for the full branching word orbit in `G_{4,q}`, while
(H2.1) is one deterministic coefficient path and no natural balanced decimal
label or index-to-word coding is given. Thus the same explicit missing equality
(H1.7) remains. H2 survives only as a possible branching model, not as a
deterministic recurrence transfer.

## 7. Candidate M1: Rudin--Shapiro Mahler cocycle

### 7.1 Exact recurrence

S5 defines, for every integer `s>=0`,

\[
 P_0(z)=Q_0(z)=1,
\]
\[
 P_{s+1}(z)=P_s(z)+z^{2^s}Q_s(z),\qquad
 Q_{s+1}(z)=P_s(z)-z^{2^s}Q_s(z).                     \tag{M1.1}
\]

Equivalently,

\[
 \binom{P_{s+1}}{Q_{s+1}}=
 \begin{pmatrix}1&z^{2^s}\\1&-z^{2^s}\end{pmatrix}
 \binom{P_s}{Q_s}.                                   \tag{M1.2}
\]

Let `epsilon_j` be the coefficient of `z^j` in `P_s` for any `s` with
`2^s>j`; (M1.1) makes this independent of `s`. Define

\[
 R(z)=\sum_{j\ge0}\varepsilon_jz^j,\qquad
 S(z)=\sum_{j\ge0}(-1)^j\varepsilon_jz^j=R(-z)
 \quad(|z|<1).
\]

Coefficient splitting, equivalently
`epsilon_{2j}=epsilon_j` and
`epsilon_{2j+1}=(-1)^j epsilon_j`, gives the associated two-component
2-Mahler equation

\[
 \binom{R(z)}{S(z)}=
 \begin{pmatrix}1&z\\1&-z\end{pmatrix}
 \binom{R(z^2)}{S(z^2)}.                            \tag{M1.3}
\]

Equation (M1.3) is an elementary reformulation of the recurrence, not a quote
from S5.

### 7.2 Congruence representation, modulus, and orbit

For every `m>=1`, specialize `z=10` and reduce modulo `q_m=10^m`. Define

\[
 p_s=P_s(10),\quad q_s=Q_s(10),\quad e_s=10^{2^s}\pmod{10^m}.
\]

The complete state and transition are

\[
 v_0=(1,1,10),\qquad
 (p,q,e)\longmapsto(p+eq,p-eq,e^2)\pmod{10^m}.        \tag{M1.4}
\]

This deterministic orbit is fully defined for all `s>=0`. Let
`s_0=ceil(log_2 m)`. Then `e_s=0 mod 10^m` for every `s>=s_0`. Hence

\[
 v_s=(p,q,0)\Longrightarrow v_{s+1}=(p,p,0)
 \Longrightarrow v_{s+2}=v_{s+1}.                   \tag{M1.5}
\]

The preperiod plus period is at most `ceil(log_2 m)+2`. Also the cocycle matrix
has determinant `-2e_s`, never a unit modulo `10^m`; it is not a congruence
group walk.

### 7.3 Source theorem and quantifiers

S5, equation (1.1) on printed page 359 (arXiv page 2), states for every
`s>=0` and every `|z|=1`, with `N=2^s`,

\[
 |P_s(z)|^2+|Q_s(z)|^2=2^{s+1}=2N.                  \tag{M1.6}
\]

Therefore

\[
 \sup_{\theta\in\mathbb R}
 |P_s(e^{2\pi i\theta})|\le\sqrt{2N}.               \tag{M1.7}
\]

S7, Theorem B on printed page 1900, additionally states that for every fixed
Gowers order `k` there exists `c(k)>0` with the Rudin--Shapiro sequence having
`U^k[N]=O(N^{-c(k)})` as `N` tends to infinity. This is fixed-order symbolic
uniformity, not the phase estimate required below.

### 7.4 Displayed T10 substitution and first failure

If (counterfactually) (M1.7) bounded the unweighted T10 sum of length `J`, it
would contradict the displayed T10 lower threshold once

\[
 \sqrt{2J}\le{J\over131072A^2n^2}
 \quad\Longleftrightarrow\quad
 J\ge2(131072)^2A^4n^4=2^{35}A^4n^4.                 \tag{M1.8}
\]

But S5 actually bounds

\[
 \sum_{j<J}\varepsilon_j e(j\theta),\qquad
 \varepsilon_j\in\{-1,1\}\text{ as defined above},  \tag{M1.9}
\]

at dyadic lengths, whereas the T10 phase is

\[
 \sum_{j<J}e\bigl(h(10^r-1)10^j\pi\bigr).           \tag{M1.10}
\]

The weights, linear index phase, radix, and observable all differ. There is no
choice of one `theta` making `j theta` equal to
`h(10^r-1)10^j pi` modulo one for all `j`, and removing the signs destroys the
parallelogram identity. Thus (M1.8) is the first numerical budget one would
need, while (M1.9) versus (M1.10) is the earlier failed hypothesis.

### 7.5 Cheap kill test

**Kill M1 for decimal congruence mixing:** by (M1.5) the exact orbit freezes
after `O(log m)` steps, while congruence mixing on groups of size polynomial
in `10^m` would require depth proportional to `m`. Noninvertibility and the
explicit fixed point prevent arithmetic monodromy expansion on this
specialization.

## 8. Inspected but not retained

### 8.1 Thue--Morse, S6 and S7

S6 gives `t_{2n}=t_n`, `t_{2n+1}=-t_n`, the autocorrelation recurrence

\[
 \eta(2n)=\eta(n),\qquad
 \eta(2n+1)=-\tfrac12(\eta(n)+\eta(n+1)),
\]

and the Riesz products in equation (12). S7 gives fixed-order Gowers decay.
This system was not retained because it is a binary automatic, signed model
already covered by the T115/T121 fingerprints, has finite-state rather than
growing arithmetic monodromy, and does not evaluate (M1.10).

### 8.2 Structured multiplicative sums, S4

S4 defines `q=product p_alpha^{nu_alpha}` to have few prime factors when
`sum nu_alpha<C_0` for a fixed constant. For `q=10^m`, that sum is `2m`, so no
fixed `C_0` applies. Its Corollary 4.5 also requires, for some fixed
`delta>0`,

\[
 \operatorname{ord}_p(\theta)>q^\delta\quad\text{for every }p\mid q.
\]

For any unit modulo `10^m`, the reductions satisfy
`ord_2(theta)<=1` and `ord_5(theta)<=4`, so this condition fails for large
`m`. Theorem 4.7 requires a subgroup of size `q^delta` and still has constants
depending on the bounded factor-count parameter. Hence the source gives no
uniform exponent `epsilon_m` satisfying the minimum collision requirement

\[
 \epsilon_m\log N_m\ge\tfrac12\log(2Am).             \tag{8.1}
\]

This is a quantitative rejection, not a retained recurrence system.

### 8.3 Nonlinear fractal Fourier decay, S8

S8, Theorem 1.2 on preprint page 4, requires a finite analytic IFS with at
least one non-affine map and then gives constants `C,eta>0` for every
self-conformal measure. The decimal map and its inverse branches are affine,
so the nonlinearity hypothesis fails. Replacing them by a nonlinear IFS gives
an ambient measure, not a named deterministic fiber. This repeats the T104
ambient-measure boundary and was not retained.

## 9. Mandatory prior-fingerprint comparison

Every prose item in this table is used only as an unverified mechanism
fingerprint unless a checked interface was separately cited in Section 3.

| Comparator and level | Normalized fingerprint | T124 separation |
|---|---|---|
| Semantic obstruction memory, unverified ledger, SHA `aa8b0f84...f76f` | Scalar bounds, regrouping, model measures, rational endpoints, or many children do not evaluate the prescribed adaptive coefficient; preserve actual orbit, carries, aliases, both frequency boxes, and phase correction. | H1/H2 deliberately stop at branching random words; M1 stops at the signed-linear/lacunary mismatch. No model endpoint is renamed as the prescribed orbit. |
| T63 audit, source claims literature-checked and deductions unverified, SHA `28e7bdc2...d59` | BBP/Zudilin rational phases fail coprimality, moving-frequency, and square-root-cost tests. | T124 uses integral monodromy quotients, not a rational approximation to the target point. H1's failure is deterministic coding, not denominator truncation. |
| T78 note, unverified proof sketch, SHA `26cc36a1...f4b` | Factorial rational truncation forces square-root modulus larger than usable orbit length. | No truncation is used. H2 instead fails at the squarefree theorem domain; M1 freezes exactly modulo `10^m`. |
| T79 note, unverified proof sketch, SHA `7fb415a8...800` | Machin rational orbit has exact order/collisions but special-numerator sums retain square-root cost. | H1 obtains genuine random-word expansion with `O(m)` depth, but no deterministic word coding. This is not special-numerator cancellation. |
| T104 note, source claims literature-checked and transfers unverified, SHA `2dee0c91...6d5` | Mahler radial scaling, torus averaging, nonlinear transfer operators, and ambient Fourier decay do not select the prescribed fiber; affine decimal dynamics fails nonlinearity. | S8 is rejected for exactly this boundary. M1 is retained only because its exact cocycle and decimal degeneration are computed, not because an ambient measure transfers. |
| T105 note, source claims literature-checked and deductions unverified, SHA `ff63d5a9...ed9f` | Energy/BSG returns unlocated structure; subgroup sums require polynomial or complete orbit lengths, not logarithmic ones. | H1 changes the model to a branching expander walk and derives its collision count directly. S4 is rejected when its decimal order hypotheses fail. |
| T112 note, source claims literature-checked and transfers unverified, SHA `72884fc7...fa` | Carry chains and Rudin--Shapiro are finite-state/random calibrations with wrong observable or excessive boundary load. | M1 reuses no T112 conclusion: it independently quotes S5 and computes the exact `z=10` congruence freeze, then displays the T10 phase mismatch. |
| T114 note, source claims literature-checked and determinant deductions unverified, SHA `db21ac7d...cca` | Interpolation determinants lose rank/height and fixed-lag recurrences do not aggregate over all decimal differences. | H1/H2 use monodromy expansion rather than determinant nonvanishing; the surviving random model still lacks the actual decimal index coding. |
| T115 note, source claims literature-checked and recursion deductions unverified, SHA `29cd0707...a36` | Base-ten substitution Riesz coefficients have a persistent decimal-ray spike. | M1 is the binary Rudin--Shapiro flat cocycle, not the base-ten Thue--Morse Riesz system. Its separate obstruction is congruence freezing and phase mismatch. |
| T117 note, source claims literature-checked and calculations unverified, SHA `ee697420...30b` | Legendre subset-character expansion gives logarithmic pattern control but needs an unsourced trace map. | H1's branching collision estimate is group spectral mixing, not Weil subset expansion. Both expose a missing pointwise coding, so no transfer advantage is claimed. |
| T118 note, source claims literature-checked and deductions unverified, SHA `2ed7a176...410e` | Private prime-power order gives separation but available exponential-sum estimates require polynomial length. | H1 avoids short deterministic sums by averaging exponentially many words; this is precisely why its mechanism does not control one consecutive orbit. |
| Rejected T119 attempt, unverified, recovered SHA `773046a3...69fa` | Predictive/Hankel/Prony rank was proposed from collision concentration; the record itself lists failures, and review rejected its prior comparison. | T124 makes no low-rank inference and uses T119 only as a rejected warning. H1/H2 matrix dimensions are monodromy dimensions, not collision Hankel ranks. |
| T120 note, source claims literature-checked and deductions unverified, SHA `8b375d1c...6dad5` | Countable renewal models have random-path theorems, exceptional high-collision paths, and no uniform growing-depth control. | H1 also separates walk-law mixing from one path. Its finite congruence gap is uniform in `m`, but no deterministic path consequence follows. |
| T121 note, source claims literature-checked and deductions unverified, SHA `01b97953...cf2` | Aggregate Walsh/Legendre energy can avoid pointwise subset loss, while automatic fixed-order norms miss growing-order mass. | S7 is screened rather than relabeled. H1 controls complete endpoint collision energy by a spectral gap, but only in a branching congruence model. |
| Active T122 | No readable artifact, source pin, or result was present; only an active lease was visible. | No fingerprint is inferred and no novelty claim is made against unavailable content. |
| Active T123 | No readable artifact, source pin, or result was present; only an active lease was visible. | No fingerprint is inferred and no novelty claim is made against unavailable content. |

The full hashes and exact report line ranges are in `SOURCE_PINS.md`.

## 10. Separately stated pi-specific transfer premise

The following is a required additional premise, not a conclusion, source
statement, conjecture endorsed by this note, or consequence of expansion.

`PI-MON-T` (unproved transfer premise): for unbounded `m`, there would have to
exist one retained system, lengths `L_m`, a prefix size `N_m`, words `w_{m,j}`
in its fixed monodromy generators for every `0<=j<N_m`, and labels
`lambda_m` on the congruence orbit such that all of the following hold
simultaneously:

1. `lambda_m(gamma(w_{m,j}))` equals the length-`m` decimal cylinder code of
   the prescribed base-ten orbit at index `j`.
2. Equality of labels preserves the ordered, diagonal-inclusive collision
   statistic, including adjacent-cylinder corrections needed for strict circle
   distance.
3. The empirical set of the prescribed words inherits the same spectral
   discrepancy as the full branching walk, with error small enough for
   (4.4)--(4.6), or it preserves the exact T10 phases with the bound (M1.8).
4. The construction is coherent on one increasing family of prefixes and, if
   used for T107, retains its boundary load, aliases, both frequency boxes, and
   every triangular row.

No inspected source supplies any clause of `PI-MON-T` for the prescribed
point. H1 fails at clauses 1 and 3; H2 fails before clause 3 on decimal moduli;
M1 fails clauses 1 and 3 and has the short orbit (M1.5).

## 11. Scope and endpoint

What survives is narrow but genuine: H1 shows that arithmetic monodromy plus
all-modulus congruence expansion yields the exact ordered collision scale for
a branching related model in `O(m)` word depth. The cheapest transfer test is
whether a deterministic recurrence index can be coded by a spectrally typical
set of monodromy words with a natural balanced decimal label. None of H1, H2,
or M1 passes that test in the inspected sources.

This note establishes no property of the fixed decimal orbit and no conclusion
about either program conjecture. Finite replay checks are not evidence for a
universal statement.

**Verdict: hold as model.** H1 is retained as an arithmetic-congruence
branching model, H2 as a squarefree branching model with an unaudited
all-quotient possibility, and M1 is quantitatively rejected for this route.

**Bounded successor (one):** For H1 only, derive the cleared coefficient state
`U_n=36^n(n!)^2a_n` modulo `10^m` and, for `1<=m<=8`, measure the deterministic
orbit length and coordinate-fiber imbalance. Stop immediately if a 2-adic or
5-adic valuation reaches `m` before depth `m`; label the output `experiment`.
