# T59: aggregate Fejer criterion for one literal T14 row

Status: `proof sketch`. The T14 and T25 interfaces and the scalar Fejer
identities cited below are machine-checked. The tensor aggregation and norm
calculation in this note are rigorous prose, not new Lean theorems.

The terminal result is a constant-explicit sufficient Fourier-and-boundary
inequality for one literal T14 row. It is not a claim that the inequality
holds for the fixed `pi` orbit. In particular, this note proves neither C2,
canonical C1, nor the canonical near-return question.

## 1. Immutable statement, provenance, and normalized scope

The canonical statement is the local formulation
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`; it has no external
original source URL. Its verified SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

It asks whether, for the ordered and diagonal-inclusive count

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\},
\]

one has

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \ \forall n\geq n_0\ \exists N\geq1:
 \qquad AnQ_\pi(n,N)\leq N^2.                    \tag{1.1}
\]

Here `N` may depend on `A,n`; the circle inequality is strict; and `pi`, base
10, and consecutive powers are fixed. T59 does not change any of these
quantifiers. It studies only a conditional finite Fourier route to one row of
T14's C2 interface.

The potentially ambiguous terms in this note are fixed as follows.

1. A "row" means one depth `ell` and one finite cutoff `P=N(k)` occurring
   below a T25 triangle depth `m`, so `ell<m`; it is not a complete triangle.
2. Every cylinder is half-open. Boundary visits are retained explicitly.
3. "Collected coefficient norm" means that all parent labels are summed and
   all equal numerical frequency pairs `(h,k)` are collected before absolute
   values are taken.
4. "Subexponential loss" below refers to this collected coefficient norm,
   not to the largest frequency queried. The latter remains exponential in
   the decimal depth.
5. All displayed finite calculations are exact formulas or explicit proved
   estimates. No bounded experiment is used as evidence for C2 or for a
   fixed-`pi` claim.

## 2. Kernel-checked inputs

The proof uses the following machine-checked interfaces without reproving
them. T14's replay record states the allowed axiom output
`propext`, `Classical.choice`, and `Quot.sound`; the T25 endpoints are
registered in `audit/AxiomAudit.lean:1338-1347`; and each cited Fejer endpoint
is included in the source module's concluding `#print axioms` block at lines
1575-1577. The new prose deductions remain only a `proof sketch`.

| Input | SHA-256 | Exact use |
|---|---|---|
| `knowledge_library/t7/FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | orbit coordinate and exact half-open decimal-cylinder code, lines 55-101 |
| `knowledge_library/t9/SuccessorSplitting.lean` | `1ee132366d7bd7f3685e37dd4258f2d28c3c386badce71fb6f3bbd845156e354` | successor fibers/counts and exact parent/child energy refinement, lines 21-47 and 71-150 |
| `knowledge_library/t14/CoherentSuccessorSplitting.lean` | `bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833` | the one-tenth parent lower bound and `energy_decrement_implies_quantitativeSplittingLevel`, lines 58-73 and 125-191 |
| `knowledge_library/t25/FiniteMultilevelEnvelope.lean` | `cea4870d7c0d254df9e18d203dee6307c50feb5bcf0d04379c00afb8eaa3aa1f` | literal `rowThreshold` and its equivalence with a T14 splitting level, lines 63-76 |
| `TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean` | `da5f190dd776ebb211ada5960c17e0e0580adce5d9c2e0d9b670b16245b31c33` | exact interval coefficient, Fejer expansion, inverse-square tail, pointwise boundary error, and estimator expansion, lines 275-403, 481-582, 846-927, and 968-1227 |

The first T14 is the successor-splitting theorem in this program. The third
file is the separately named boundary-robust Fejer T14 from the block-hitting
program. This note never conflates their claims.

## 3. One literal T14/T25 row

Fix integers

\[
 \ell\geq1,\qquad P\geq1,\qquad q=10^\ell.        \tag{3.1}
\]

In a literal T25 triangle, `P` is one value `N(k)` and `ell<m<=k`. Put

\[
 x_j=\operatorname{fract}(10^j\pi)\in[0,1),
 \qquad 0\leq j<P.                                \tag{3.2}
\]

For `0<=a<q` and `0<=d<10`, define the parent and successor cylinders

\[
 I_a=[a/q,(a+1)/q),                                \tag{3.3}
\]

\[
 J_{a,d}=[(10a+d)/(10q),(10a+d+1)/(10q)).         \tag{3.4}
\]

Their literal finite counts are

\[
 A_a=\sum_{j<P}{\bf1}_{I_a}(x_j),\qquad
 C_{a,d}=\sum_{j<P}{\bf1}_{J_{a,d}}(x_j).          \tag{3.5}
\]

The ten children partition their parent, including the half-open endpoint
convention, so

\[
 A_a=\sum_{d=0}^9 C_{a,d}.                         \tag{3.6}
\]

Write

\[
 E_q=\sum_{a=0}^{q-1}A_a^2,
 \qquad
 E_{10q}=\sum_{a=0}^{q-1}\sum_{d=0}^9C_{a,d}^2.   \tag{3.7}
\]

The machine-checked T7 theorem `piCylinderCode_eq_decimalCode`, lines 63-101,
identifies `piCylinderCode ell j` with the half-open decimal-cylinder code of
the orbit point (3.2). Hence the indices counted by `A_a` are exactly
`piCylinderFiber ell P a`. The checked successor definition appends the digit
`d`, so the indices counted by `C_{a,d}` are exactly the corresponding
`piSuccessorFiber`. Therefore (3.7) is exactly
`piCylinderCollisionEnergy ell P` and
`piCylinderCollisionEnergy (ell+1) P` under the checked successor refinement.

For `eta>0`, parent `a` is split when

\[
 \exists d\ne e:\qquad
 C_{a,d}\geq\eta A_a,\quad C_{a,e}\geq\eta A_a.  \tag{3.8}
\]

Equivalently, if

\[
 s_a=\max_{d\ne e}\min(C_{a,d},C_{a,e}),          \tag{3.9}
\]

then `a` is split exactly when `eta A_a<=s_a`. Define the split-parent
collision mass and the literal row defect by

\[
 M_\eta=\sum_{a=0}^{q-1}{\bf1}_{\{\eta A_a\leq s_a\}}A_a^2,
 \qquad
 \Delta_{\mu,\eta}=\mu E_q-M_\eta.                \tag{3.10}
\]

T25's `rowThreshold ell P eta mu`, equivalently T14's
`QuantitativeSplittingLevel ell P mu eta`, is literally

\[
 \boxed{\Delta_{\mu,\eta}\leq0},
 \quad\text{that is}\quad
 \boxed{\mu E_q\leq M_\eta}.                      \tag{3.11}
\]

No parent selector has been smoothed or replaced in (3.11).

## 4. Expanding the nonlinear splitting defect

The split selector in (3.10) is discontinuous and depends on all ten counts.
Rather than falsely Fourier-expand that selector, use T14's checked reverse
energy bridge.

For `0<eta<=1/10`, set

\[
 \lambda_\eta=(1-9\eta)^2.                        \tag{4.1}
\]

For every split parent, Cauchy-Schwarz and (3.6) give

\[
 \sum_d C_{a,d}^2\geq A_a^2/10.                  \tag{4.2}
\]

If `a` is not split, at most one child can have count at least `eta A_a`.
The other nine have total count at most `9 eta A_a`, so one child has count
at least `(1-9 eta)A_a`. Hence

\[
 \sum_d C_{a,d}^2\geq\lambda_\eta A_a^2.         \tag{4.3}
\]

Summing (4.2) over split parents and (4.3) over nonsplit parents yields

\[
 E_{10q}\geq {1\over10}M_\eta+
   \lambda_\eta(E_q-M_\eta).                     \tag{4.4}
\]

If in addition `lambda_eta>1/10`, division by the positive coefficient
`lambda_eta-1/10` gives

\[
 M_\eta\geq
 {\lambda_\eta E_q-E_{10q}\over
  \lambda_\eta-1/10}.                            \tag{4.5}
\]

Choose the fixed constants

\[
 \eta={1\over100},\qquad \rho={1\over2},
 \qquad \lambda_\eta={8281\over10000},          \tag{4.6}
\]

\[
 \gamma=\rho-{1\over10}={2\over5},
 \qquad
 \mu={\lambda_\eta-\rho\over\lambda_\eta-1/10}
     ={3281\over7281}.                            \tag{4.7}
\]

These satisfy

\[
 0<\eta\leq1/10,
 \qquad 1/10<\rho<\lambda_\eta,
 \qquad 0<\mu<1.                                 \tag{4.8}
\]

Substituting (4.7) into (3.10) and using (4.5) gives the promised aggregate
expansion of the literal splitting defect:

\[
 \boxed{
 \Delta_{\mu,\eta}\leq
 {E_{10q}-\rho E_q\over\lambda_\eta-1/10}.}       \tag{4.9}
\]

Consequently

\[
 E_{10q}\leq\rho E_q
 \quad\Longrightarrow\quad
 \Delta_{\mu,\eta}\leq0,                        \tag{4.10}
\]

which is exactly the checked T14 implication, now with every constant shown.

## 5. Explicit finite Fejer approximants

Write

\[
 e(t)=\exp(2\pi i t).                              \tag{5.1}
\]

For an integer order `H>=0`, use the mean-one Fejer kernel

\[
 K_H(t)={1\over H+1}\left|\sum_{r=0}^H e(rt)\right|^2
 =\sum_{|h|\leq H}w_H(h)e(ht),                    \tag{5.2}
\]

where

\[
 w_H(h)=1-{|h|\over H+1}\quad(|h|\leq H),
 \qquad w_H(h)=0\quad(|h|>H).                     \tag{5.3}
\]

For `Q>=1` and `0<=b<Q`, let `I_{Q,b}=[b/Q,(b+1)/Q)` and choose the finite
approximant

\[
 F_{Q,b,H}(x)=\int_{-1/2}^{1/2}
 K_H(t){\bf1}_{I_{Q,b}}(x-t)\,dt,                 \tag{5.4}
\]

with periodic interpretation of the indicator. Define

\[
 \sigma_Q(h)=
 \begin{cases}
  1/Q,&h=0,\\[1mm]
  \sin(\pi h/Q)/(\pi h),&h\ne0.
 \end{cases}                                      \tag{5.5}
\]

The checked interval integral and Fejer expansion give the exact finite
coefficient formula

\[
 \boxed{
 F_{Q,b,H}(x)=\sum_{|h|\leq H}c_{Q,b,H}(h)e(hx),}
                                                               \tag{5.6}
\]

\[
 \boxed{
 c_{Q,b,H}(h)=w_H(h)\sigma_Q(h)
 e\!\left(-{h(b+1/2)\over Q}\right).}             \tag{5.7}
\]

In particular, `c(0)=1/Q`. The parent approximants are (5.4) with

\[
 Q=q,\quad b=a,\quad H=H_0,                       \tag{5.8}
\]

and the successor approximants are (5.4) with

\[
 Q=10q,\quad b=10a+d,\quad H=H_1.                \tag{5.9}
\]

The concrete widths and orders used from now on are

\[
 \delta_0={1\over4q^2},\qquad H_0=40q^3,          \tag{5.10}
\]

\[
 \delta_1={1\over4(10q)^2}={1\over400q^2},
 \qquad H_1=8000q^3.                              \tag{5.11}
\]

Since `q>=10`, both widths are strictly below half the corresponding cylinder
length. Thus all boundary neighborhoods below are disjoint at each grid
scale.

## 6. Every boundary and smoothing error

The checked inverse-square estimate gives, for `0<delta<=1/2`,

\[
 \int_{\delta\leq|t|\leq1/2}K_H(t)\,dt
 \leq {1\over2(H+1)\delta}.                       \tag{6.1}
\]

If `x` has circular distance at least `delta` from both endpoints of
`I_{Q,b}`, then

\[
 |F_{Q,b,H}(x)-{\bf1}_{I_{Q,b}}(x)|
 \leq\varepsilon(H,\delta),
 \qquad
 \varepsilon(H,\delta)={1\over2(H+1)\delta}.      \tag{6.2}
\]

Always `0<=F_{Q,b,H}(x)<=1`. For completeness, the individual cylinder
boundary count is

\[
 \mathcal B_{Q,b}(\delta)=
 \#\{j<P:\operatorname{dist}(x_j,b/Q)<\delta
 \text{ or }
 \operatorname{dist}(x_j,(b+1)/Q)<\delta\}.       \tag{6.3}
\]

The checked scalar estimator bound is therefore

\[
 \left|\sum_{j<P}F_{Q,b,H}(x_j)
  -\sum_{j<P}{\bf1}_{I_{Q,b}}(x_j)\right|
 \leq \mathcal B_{Q,b}(\delta)+P\varepsilon(H,\delta).
                                                               \tag{6.4}
\]

Summing (6.4) directly would introduce an avoidable factor `Q`. To retain all
parent cancellation, define instead the union boundary count

\[
 B_Q(\delta)=
 \#\{j<P:\min_{0\leq r<Q}
 \operatorname{dist}(x_j,r/Q)<\delta\}.           \tag{6.5}
\]

Because `Q>=2` and `delta<1/(2Q)` at both scales used here, every boundary
visit in (6.5) belongs to exactly the two adjacent individual boundary counts,
including the wraparound endpoint:

\[
 \sum_{b=0}^{Q-1}\mathcal B_{Q,b}(\delta)=2B_Q(\delta).         \tag{6.6}
\]

There is a sharper vector calculation. The half-open cylinders partition the
circle, `K_H` is nonnegative of mass one, and hence

\[
 \sum_{b=0}^{Q-1}F_{Q,b,H}(x)=1.                \tag{6.7}
\]

For a sample outside (6.5), the smoothed probability vector differs in
`ell^1` from its one-hot cylinder vector by at most `2 epsilon(H,delta)`.
For a boundary sample the distance is at most `2`. Therefore, if

\[
 A_{Q,b}=\sum_{j<P}{\bf1}_{I_{Q,b}}(x_j),
 \qquad
 \widetilde A_{Q,b}=\sum_{j<P}F_{Q,b,H}(x_j),     \tag{6.8}
\]

then

\[
 \sum_b|\widetilde A_{Q,b}-A_{Q,b}|
 \leq2B_Q(\delta)+{P\over(H+1)\delta}.            \tag{6.9}
\]

Both counts in (6.8) lie in `[0,P]`. Multiplying (6.9) by the bound `2P` for
`A_{Q,b}+tilde A_{Q,b}` gives the complete aggregate energy error

\[
 \boxed{
 |\widetilde E_{Q,H}-E_Q|
 \leq4P B_Q(\delta)+{2P^2\over(H+1)\delta},}       \tag{6.10}
\]

where

\[
 \widetilde E_{Q,H}=\sum_{b=0}^{Q-1}\widetilde A_{Q,b}^2.
                                                               \tag{6.11}
\]

Formula (6.10) lists the only two errors: actual visits to the union of grid
boundary neighborhoods, and the Fejer tail away from that union. No endpoint
is discarded.

For the concrete choices (5.10)-(5.11), these two scale errors are

\[
 |\widetilde E_{q,H_0}-E_q|
 \leq4P B_q(\delta_0)+
 {8q^2P^2\over40q^3+1},                           \tag{6.12}
\]

\[
 |\widetilde E_{10q,H_1}-E_{10q}|
 \leq4P B_{10q}(\delta_1)+
 {800q^2P^2\over8000q^3+1}.                      \tag{6.13}
\]

In particular,

\[
 {1\over2}\,{8q^2P^2\over40q^3+1}
 <{P^2\over10q},
 \qquad
 {800q^2P^2\over8000q^3+1}< {P^2\over10q}.       \tag{6.14}
\]

## 7. Summing all parents before taking norms

For `h in Z`, put

\[
 S_P(h)=\sum_{j=0}^{P-1}e(hx_j).                  \tag{7.1}
\]

Expanding (6.11) with (5.6), then summing the parent label `b` first, gives

\[
 \widetilde E_{Q,H}
 =\sum_{|h|,|k|\leq H}D_{Q,H}(h,k)S_P(h)S_P(k),  \tag{7.2}
\]

where the geometric sum over `b` is exact:

\[
 \sum_{b=0}^{Q-1}
 e\!\left(-{(h+k)(b+1/2)\over Q}\right)
 =\begin{cases}
 Q(-1)^{(h+k)/Q},&Q\mid h+k,\\
 0,&Q\nmid h+k.
 \end{cases}                                      \tag{7.3}
\]

Consequently the fully collected coefficient is

\[
 \boxed{
 D_{Q,H}(h,k)=
 \begin{cases}
 Q(-1)^{(h+k)/Q}w_H(h)w_H(k)\sigma_Q(h)\sigma_Q(k),
   &Q\mid h+k,\quad |h|,|k|\leq H,\\
 0,&\text{otherwise}.
 \end{cases}}                                     \tag{7.4}
\]

This includes every alias `h+k` equal to an arbitrary multiple of `Q`; it is
not restricted to `k=-h`. The zero coefficient is

\[
 D_{Q,H}(0,0)=1/Q.                                \tag{7.5}
\]

If exactly one of `h,k` is zero, divisibility in (7.4) forces the other to be
a nonzero multiple of `Q`, and then `sigma_Q` vanishes. Thus

\[
 D_{Q,H}(0,k)=D_{Q,H}(h,0)=0
 \quad(h,k\ne0).                                  \tag{7.6}
\]

For the energy defect, pad the two finite arrays by zero and define

\[
 C_\rho(h,k)=D_{10q,H_1}(h,k)-\rho D_{q,H_0}(h,k).              \tag{7.7}
\]

Its zero mode is

\[
 \boxed{C_\rho(0,0)={1\over10q}-{\rho\over q}
 =-{\gamma\over q}=-{2\over5q}.}               \tag{7.8}
\]

Let

\[
 \mathcal R_{\ell,P}=
 \sum_{(h,k)\ne(0,0)}C_\rho(h,k)S_P(h)S_P(k).    \tag{7.9}
\]

By (7.6), every term in (7.9) has both frequencies nonzero.

## 8. Exact collected coefficient norms

The following calculation is after all parents and all equal numerical
frequencies have been collected. For a residue `r mod Q`, define

\[
 U_r(Q,H)=
 \sum_{\substack{|h|\leq H\\h\equiv r\pmod Q}}
 w_H(h)|\sigma_Q(h)|,                            \tag{8.1}
\]

\[
 V_r(Q,H)=
 \sum_{\substack{|h|\leq H\\h\equiv r\pmod Q}}
 w_H(h)^2\sigma_Q(h)^2.                           \tag{8.2}
\]

Because `U_{-r}=U_r` and `V_{-r}=V_r`, (7.4) gives the exact finite identities

\[
 \boxed{\|D_{Q,H}\|_1
 =Q\sum_{r\bmod Q}U_r(Q,H)^2,}                    \tag{8.3}
\]

\[
 \boxed{\|D_{Q,H}\|_2^2
 =Q^2\sum_{r\bmod Q}V_r(Q,H)^2.}                  \tag{8.4}
\]

For residue zero, all nonzero terms are multiples of `Q` and have
`sigma_Q(h)=0`. Hence

\[
 U_0(Q,H)=1/Q,\qquad V_0(Q,H)=1/Q^2,             \tag{8.5}
\]

and these contributions are exactly the single coefficient (7.5).

We now bound the nonzero part with constants. Put

\[
 L=\max(1,\lceil H/Q\rceil).                      \tag{8.6}
\]

Fix `r!=0`. The two representatives of `r` in `(-Q,Q)` each satisfy
`|sigma_Q(h)|<=1/Q`, by `|sin u|<=|u|`. In every later `Q`-shell there are at
most two representatives, and the shell `n>=1` contributes at most
`2/(nQ)`. Since

\[
 \sum_{n=1}^L{1\over n}\leq1+\log L,             \tag{8.7}
\]

we obtain

\[
 U_r(Q,H)\leq{2(2+\log L)\over Q}.                \tag{8.8}
\]

Similarly the two nearest squares contribute at most `2/Q^2`, while all
later shells contribute at most

\[
 {2\over\pi^2Q^2}\sum_{n=1}^{\infty}{1\over n^2}
 ={1\over3Q^2}.                                   \tag{8.9}
\]

Thus

\[
 V_r(Q,H)\leq{7\over3Q^2}.                        \tag{8.10}
\]

Delete the zero pair and write a star. Equations (8.3)-(8.10) imply

\[
 \boxed{\|D_{Q,H}^{*}\|_1
 \leq4(2+\log L)^2,}                              \tag{8.11}
\]

\[
 \boxed{\|D_{Q,H}^{*}\|_2
 \leq{7\over3\sqrt Q}.}                          \tag{8.12}
\]

The exact norm of the combined defect is, without hidden labels,

\[
 \boxed{
 \|C_\rho^*\|_1=
 \sum_{(h,k)\ne(0,0)}
 |D_{10q,H_1}(h,k)-\rho D_{q,H_0}(h,k)|.}          \tag{8.13}
\]

Equivalently, (8.13) splits into the terms with `q|(h+k)` but
`10q` not dividing `h+k`, where only `rho D_{q,H_0}` remains, and the terms
with `10q|(h+k)`, where the two displayed coefficients are subtracted before
the absolute value. This is the complete collision accounting between the two
scales.

For the concrete orders,

\[
 L_0=H_0/q=40q^2,
 \qquad L_1=H_1/(10q)=800q^2.                    \tag{8.14}
\]

The triangle inequality applied only after the collection (8.13) gives

\[
 \boxed{
 \|C_\rho^*\|_1\leq K_\ell:=
 4\left[(2+\log(800q^2))^2+
 {1\over2}(2+\log(40q^2))^2\right].}             \tag{8.15}
\]

Likewise,

\[
 \boxed{
 \|C_\rho^*\|_2\leq
 {7\over3}\left({1\over\sqrt{10q}}+
 {1\over2\sqrt q}\right).}                      \tag{8.16}
\]

Since `q=10^ell`, (8.15) is `O(ell^2)`. The apparent sum over `10^ell`
parents has therefore not produced an exponential coefficient norm.

## 9. Full defect inequality with all errors collected

Equations (7.2), (7.7), and (7.8) give the exact smoothed identity

\[
 \widetilde E_{10q,H_1}-\rho\widetilde E_{q,H_0}
 =-{2P^2\over5q}+\mathcal R_{\ell,P}.             \tag{9.1}
\]

Using (6.12)-(6.14) in both directions gives

\[
\begin{split}
 E_{10q}-\rho E_q
 \leq{}&-{2P^2\over5q}+|\mathcal R_{\ell,P}|\\
 &+4P\left(B_{10q}(\delta_1)+{1\over2}B_q(\delta_0)\right)\\
 &+{800q^2P^2\over8000q^3+1}
 +{4q^2P^2\over40q^3+1}.                         \tag{9.2}
\end{split}
\]

The final line is strictly less than `P^2/(5q)` by (6.14). Thus every term in
the passage from exact counts to the Fourier tensor is visible in (9.2).

## 10. Constant-explicit implication to the literal row

Assume the two finite conditions

\[
 \boxed{
 B_{10q}\!\left({1\over400q^2}\right)
 +{1\over2}B_q\!\left({1\over4q^2}\right)
 \leq {P\over40q},}                              \tag{10.1}
\]

\[
 \boxed{
 |\mathcal R_{\ell,P}|\leq {P^2\over10q}.}        \tag{10.2}
\]

Then the boundary line in (9.2) is at most `P^2/(10q)`, the Fourier remainder
is at most `P^2/(10q)`, and the tail line is strictly less than
`P^2/(5q)`. Their sum is strictly less than the zero-mode margin
`2P^2/(5q)`. Therefore

\[
 E_{10q}-{1\over2}E_q<0.                          \tag{10.3}
\]

Combining (10.3) with (4.9) proves the literal T14/T25 row

\[
 \boxed{
 {3281\over7281}E_q
 \leq
 \sum_{a=0}^{q-1}
 {\bf1}_{\{A_a/100\leq s_a\}}A_a^2.}             \tag{10.4}
\]

This is a fixed positive splitting statement with parameters independent of
`ell` and `P`.

For a conventional one-frequency hypothesis, (7.6) and (8.15) show that
(10.2) follows from

\[
 |S_P(h)|\leq\beta_\ell P
 \quad\text{for every }0<|h|\leq8000q^3,          \tag{10.5}
\]

and

\[
 \boxed{\beta_\ell^2 K_\ell\leq{1\over10q}.}     \tag{10.6}
\]

Indeed, each product in (7.9) is then at most `beta_ell^2 P^2` in modulus,
and summation against the already collected norm (8.13) gives (10.2).

Conditions (10.1), (10.5), and (10.6), with the displayed `q`, orders,
widths, and `K_ell`, are the promised constant-explicit finite
Fourier-and-boundary implication to one literal T14 row.

## 11. Depth-loss verdict

The cancellation-first architecture does have subexponential aggregate
coefficient loss:

\[
 \|C_\rho^*\|_1=O(\ell^2),                        \tag{11.1}
\]

while the T14 parameters

\[
 \eta=1/100,\qquad\mu=3281/7281                  \tag{11.2}
\]

remain fixed and positive. Root-of-unity orthogonality (7.3), including all
aliases, is what removes the naive factor `10^ell`. Thus this architecture is
not retired by an exponential coefficient-norm lower bound.

There are still two exponential-scale analytic requirements:

1. the largest queried frequency is `H_1=8000*10^(3 ell)`;
2. (10.6) asks for cancellation of order approximately
   `10^(-ell/2)/ell`, and (10.1) asks for boundary incidence of order
   `P*10^(-ell)`.

These are stated hypotheses, not verified properties of the fixed `pi` orbit.
The conclusion is therefore a finite fixed-`pi` analytic frontier, not C2:
prove (10.1) and either the aggregate inequality (10.2) or the stronger
one-frequency conditions (10.5)-(10.6) on enough coherent rows.

## 12. Claim boundary

This note establishes, at `proof sketch` level, the finite implication
(10.1)-(10.2) implies (10.4). It uses machine-checked T14 and T25 only for the
literal combinatorial interface and reverse energy bridge, and a separately
machine-checked Fejer module for (5.6), (6.1), and (6.2).

It does not establish (10.1), (10.2), or (10.5) for `pi`; it does not provide
the coherent sequence of rows required by T14; and it makes no C2, canonical
C1, canonical A1, normality, or local decimal-block claim.
