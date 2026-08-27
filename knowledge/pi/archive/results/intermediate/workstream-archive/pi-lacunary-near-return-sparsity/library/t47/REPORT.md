# T47: the T37 stream satisfies the existential T14 sibling

Status: `proof sketch` built from the vendored kernel-checked T14 and T37
modules. The deductions specific to the represented real, Haar convergence,
and the stream predicates below are rigorous prose, not new Lean theorems.

Every conclusion in this report is about one explicit artificial-stream
A13/A14 sibling. Nothing here is a statement about `Real.pi`, canonical C2,
canonical C1, canonical A1, or decimal digits of `pi`.

## 1. Immutable statement, normalization, and scope

The byte-identical `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The local canonical question has no external original source URL. Its
provenance is preserved verbatim in `canonical_statement.txt`. In normalized
form it asks whether

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \ \forall n\geq n_0\ \exists N\geq1:\qquad
 A n Q_\pi(n,N)\leq N^2,                                      \tag{1.1}
\]

where pairs are ordered, the diagonal is included, and the circle-distance
inequality in `Q_pi` is strict. This report changes `pi` to an explicitly
represented artificial real. It therefore addresses only the recorded sibling
ambiguities A13 and A14. It does not change the quantifiers in (1.1), and it
does not claim a transfer back to `pi`.

The quantifier ambiguity central to T47 is separate from A1. T14's coherent
splitting condition chooses one increasing checkpoint sequence existentially.
Its literal negation must defeat every admissible checkpoint sequence and weak
limit. Bad behavior on one displayed family cannot establish that negation.

## 2. Kernel-checked inputs

The two vendored files are reused, not reproved:

| File | SHA-256 | Exact uses |
|---|---|---|
| `T14CoherentSuccessorSplitting.lean` | `bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833` | coherent predicate and triangular quantifiers, lines 26-55; literal quantified failure, lines 592-626; weighted-dominance package, lines 628-655 |
| `T37ArtificialStreamObstruction.lean` | `aa0979b629131c6e30c2d8a8dc8c70499ff03d98cd35b2f49841f7669585116c` | stream and checkpoints, lines 201-333; exact core/error counts, lines 449-515 and 721-767; leakage limit, lines 1083-1245; moving root, lines 1247-1610; imported no-original-branch theorem, lines 1688-1763 |

Both files belong to the accumulated kernel-checked library. Their registered
axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
The T14 file does not assert C2 for `pi`; it checks the exact conditional
interface. The T37 file concerns only its artificial stream.

## 3. The fixed stream and its two checkpoints

Let `D={0,...,9}`. Write `s_j` for the natural value of
`artificialStream j` from T37. For stage `q`, put

\[
 m_q=q+1,\qquad A_q=\operatorname{stageStart}(q),               \tag{3.1}
\]
\[
 B_q=A_q+2m_q10^{m_q},\qquad
 R_q=m_q^3(B_q+1)+3,                                           \tag{3.2}
\]
\[
 L_q=R_qm_q,\qquad K_q=L_q-2m_q=(R_q-2)m_q.                    \tag{3.3}
\]

These are exactly T37's `stageOrder`, `stageErrorBudget`,
`stageRepetitions`, `seedSegmentLength`, and safe core size. The stream is
fixed before any checkpoint or thinning is chosen:

\[
 s=\operatorname{concatStream}(\operatorname{stageBlock}).      \tag{3.4}
\]

There are two distinct checkpoints:

\[
 S_q:=\operatorname{sampledCheckpoint}(q)
     =A_q+10^{m_q}L_q,                                         \tag{3.5}
\]
\[
 I_q:=\operatorname{inspectionCheckpoint}(q)=S_q+2m_q.         \tag{3.6}
\]

`S_q` limits factor starts to `0 <= j < S_q`. A factor may extend
past `S_q`; this is T37's overlapping first-start convention. `I_q` is not a
sample size. It is the prefix length sufficient to inspect every count of a
word of length at most `2m_q`. T37 machine-checks that both checkpoint
sequences are strictly increasing and that agreement through `I_q` determines
all those row entries.

For a finite word `w`, define

\[
 C_s(N,w)=\#\{0\leq j<N:(s_j,\ldots,s_{j+|w|-1})=w\}.           \tag{3.7}
\]

This is T37's `firstStartCount`. Its exact outgoing endpoint convention is

\[
 \sum_{a\in D}C_s(N,wa)=C_s(N,w).                              \tag{3.8}
\]

There is no outgoing loss because `s` is infinite and only starts are
restricted. For incoming extensions T37 instead checks the exact endpoint
identity

\[
 \sum_{a\in D}C_s(N,aw)+{\bf1}_{w\text{ occurs at }0}
 =C_s(N,w)+{\bf1}_{w\text{ occurs at }N}.                      \tag{3.9}
\]

Thus no endpoint term is hidden.

## 4. Represented real and decimal endpoint convention

Define the real represented by the fixed stream, rather than declaring an
abstract shift orbit:

\[
 x_s:=\sum_{j=0}^{\infty}s_j10^{-(j+1)}.                       \tag{4.1}
\]

The endpoint convention is the literal series (4.1), with the unique decimal
expansion that is neither eventually zero nor eventually nine. Here that
uniqueness is not an assumption. Every sufficiently late T37 stage contains a
repeated all-zero seed and a repeated all-nine seed. Since `stageStart` is
strictly increasing, every tail of `s` contains both a later zero and a later
nine. Hence neither `s` nor any tail is eventually zero or eventually nine.
In particular, `0<x_s<1`, and no sampled orbit point lies on a decimal-cylinder
endpoint.

For every `j`, let

\[
 y_j:=\sum_{r=0}^{\infty}s_{j+r}10^{-(r+1)}\in(0,1).            \tag{4.2}
\]

Multiplying (4.1) by `10^j` and separating its finite prefix gives an integer
`z_j` with

\[
 10^j x_s=z_j+y_j.                                             \tag{4.3}
\]

Therefore the literal circle orbit obtained by replacing `pi` with `x_s` is

\[
 u_s(j):=((10^j x_s):\mathbb R/\mathbb Z)=(y_j:\mathbb R/\mathbb Z). \tag{4.4}
\]

For `0<=a<10^n`, use the half-open decimal cylinder

\[
 J_{n,a}=[a10^{-n},(a+1)10^{-n}).                              \tag{4.5}
\]

The nonendpoint conclusion above makes membership in (4.5) equivalent to the
first `n` digits of the tail having code `a`. Thus (3.7) is exactly the
cylinder count of the actual orbit (4.4), not merely of a symbolic surrogate.

## 5. Literal sibling C2_s

For `N>0`, define the empirical probability measure

\[
 \sigma_{s,N}:={1\over N}\sum_{j=0}^{N-1}\delta_{u_s(j)}.       \tag{5.1}
\]

The literal sibling `C2_s`, obtained only by replacing `pi` by `x_s` in C2,
is the following proposition:

\[
\begin{split}
 \exists\alpha,C>0\ \exists M:\mathbb N\to\mathbb N\
 &\bigl[\operatorname{StrictMono}(M)\ \wedge\
       (\forall k,\ 0<M(k))\bigr]\\
 \exists\nu\in\operatorname{Prob}(\mathbb R/\mathbb Z)\quad
 &\sigma_{s,M(k)}\Rightarrow\nu,\\
 &\exists r_0>0\ \forall r\ (0<r\leq r_0\Rightarrow
   (\nu\times\nu)\{(x,y):\operatorname{dist}(x,y)\leq r\}
       \leq Cr^\alpha).
                                                               \tag{5.2}
\end{split}
\]

The closed inequality `dist<=r`, positivity of both constants, strict
increase and positivity of `M`, and the sufficiently-small-radius quantifier
are all part of (5.2).

## 6. Complete stream analogue of T14

For a word `w` of length `l` and a digit `a`, set

\[
 C_s(N,w;a):=C_s(N,wa),\qquad
 E_s(l,N):=\sum_{w\in D^l}C_s(N,w)^2.                          \tag{6.1}
\]

A parent is quantitatively split at threshold `eta` when

\[
 \operatorname{SplitParent}_s(l,N,\eta,w)\iff
 \exists a,b\in D:\ a\ne b,\quad
 \eta C_s(N,w)\leq C_s(N,w;a),\quad
 \eta C_s(N,w)\leq C_s(N,w;b).                                \tag{6.2}
\]

The level predicate, including collision-energy weighting, is

\[
 \operatorname{SplitLevel}_s(l,N,\mu,\eta)\iff
 \mu E_s(l,N)\leq
 \sum_{w\in D^l}{\bf1}_{\operatorname{SplitParent}_s(l,N,\eta,w)}
 C_s(N,w)^2.                                                    \tag{6.3}
\]

The count includes exactly the levels `l<m`:

\[
 \operatorname{SplitCount}_s(m,N,\mu,\eta)
 :=\#\{l\in\mathbb N:l<m,\ \operatorname{SplitLevel}_s(l,N,\mu,\eta)\}.
                                                                    \tag{6.4}
\]

The full fixed-parameter stream analogue of T14's predicate is

\[
\begin{split}
 \operatorname{CoherentSplitAt}_s(\mu,\eta,d,B,m_0,k_0,M,\nu)
 \iff{}&0<\mu<1\ \wedge\ 0<\eta\leq1/10\ \wedge\ 0<d\ \wedge\ 0\leq B\\
 &\wedge\ \operatorname{StrictMono}(M)\ \wedge\ (\forall k,0<M(k))\\
 &\wedge\ \sigma_{s,M(k)}\Rightarrow\nu\\
 &\wedge\ \forall k\in\mathbb N\ (k_0\leq k\Rightarrow
      \forall m\in\mathbb N\ (m_0\leq m\Rightarrow m\leq k\Rightarrow\\
 &\hspace{42mm}d m-B\leq
       \operatorname{SplitCount}_s(m,M(k),\mu,\eta))).         \tag{6.5}
\end{split}
\]

All eight witnesses `mu,eta,d,B,m0,k0,M,nu` are fixed outside both row
quantifiers. Existential coherent splitting is

\[
 \operatorname{CoherentSplit}_s\iff
 \exists\mu,\eta,d,B,m_0,k_0,M,\nu:\
 \operatorname{CoherentSplitAt}_s(\mu,\eta,d,B,m_0,k_0,M,\nu). \tag{6.6}
\]

Its literal negation, with no chosen bad checkpoint family substituted for
the universal `M`, is

\[
\begin{split}
 \forall\mu,\eta,d,B,m_0,k_0,M,\nu,\quad
 &[0<\mu<1\ \wedge\ 0<\eta\leq1/10\ \wedge\ 0<d\ \wedge\ 0\leq B\\
 &\wedge\operatorname{StrictMono}(M)\ \wedge\ (\forall k,0<M(k))
 \wedge\sigma_{s,M(k)}\Rightarrow\nu]\\
 &\Longrightarrow\exists k\geq k_0\ \exists m\geq m_0:\quad
 m\leq k\ \wedge\
 \operatorname{SplitCount}_s(m,M(k),\mu,\eta)<d m-B.           \tag{6.7}
\end{split}
\]

For completeness, T14's associated weighted-dominance conclusion uses

\[
 \operatorname{DomParent}_s(l,N,\eta,w)\iff
 \exists a\in D:\ (1-9\eta)C_s(N,w)\leq C_s(N,w;a),           \tag{6.8}
\]
\[
 \operatorname{DomEnergy}_s(l,N,\eta):=
 \sum_{w\in D^l}{\bf1}_{\operatorname{DomParent}_s(l,N,\eta,w)}C_s(N,w)^2.
                                                                    \tag{6.9}
\]

The full sibling failure package strengthens the conclusion in (6.7) by
requiring, for its bad `k,m`,

\[
 \forall l<m:\quad
 \neg\operatorname{SplitLevel}_s(l,M(k),\mu,\eta)\Rightarrow
 (1-\mu)E_s(l,M(k))<\operatorname{DomEnergy}_s(l,M(k),\eta).   \tag{6.10}
\]

The first literal clause to test is still the bad-row existence in (6.7).

## 7. Exact fixed-depth T37 counts

Fix `q` and a depth `n<=m_q`. For each `w` in `D^n`, set

\[
 e_q(w):=\operatorname{stageErrorCount}(q,w),\qquad
 c_{q,n}:=K_q10^{m_q-n}.                                      \tag{7.1}
\]

T37's checked core formula, exact core/error decomposition, and total error
formula give

\[
 C_s(S_q,w)=c_{q,n}+e_q(w),\qquad 0\leq e_q(w)\leq B_q,        \tag{7.2}
\]
\[
 \sum_{w\in D^n}e_q(w)=B_q.                                  \tag{7.3}
\]

Equations (3.2), (3.3), and (3.5) give the exact normalization

\[
 S_q=10^{m_q}K_q+B_q=10^n c_{q,n}+B_q.                        \tag{7.4}
\]

Consequently

\[
 10^n C_s(S_q,w)-S_q=10^n e_q(w)-B_q,                         \tag{7.5}
\]
\[
 {C_s(S_q,w)\over S_q}-10^{-n}
 ={e_q(w)-B_q10^{-n}\over S_q}.                               \tag{7.6}
\]

T37 machine-checks `m_q B_q<=K_q`. Since `B_q>0`, (7.4) implies

\[
 0<{B_q\over S_q}\leq{1\over1+m_q10^{m_q}}\longrightarrow0.  \tag{7.7}
\]

Thus, uniformly for all `w` and all `n<=m_q`,

\[
 \left|{C_s(S_q,w)\over S_q}-10^{-n}\right|
 \leq {B_q\over S_q}.                                        \tag{7.8}
\]

At one fixed depth, summing absolute discrepancies gives the useful explicit
total-variation estimate

\[
 \sum_{w\in D^n}\left|{C_s(S_q,w)\over S_q}-10^{-n}\right|
 \leq {2B_q\over S_q}.                                       \tag{7.9}
\]

There is also an exact collision-energy formula. Let
`E_q(n)=E_s(n,S_q)`. Expanding (7.2) and using (7.3) yields

\[
 {E_q(n)\over S_q^2}
 =10^{-n}+{\sum_{w\in D^n}e_q(w)^2-B_q^2/10^n\over S_q^2}.    \tag{7.10}
\]

Cauchy--Schwarz makes the error in (7.10) nonnegative, while
`sum_w e_q(w)^2<=B_q^2` gives

\[
 0\leq {E_q(n)\over S_q^2}-10^{-n}
 \leq (B_q/S_q)^2.                                           \tag{7.11}
\]

These are fixed-depth limits along the named T37 sampled checkpoints `S_q`.
Inspection checkpoints `I_q` certify the needed digits but never enter a
normalization.

## 8. Weak limit and the literal C2_s witness

For fixed `n`, (4.5) and (7.9) show that the masses of all depth-`n`
half-open cylinders converge to `10^{-n}`. Here is a direct weak-convergence
argument with no appeal to finite evidence. Given continuous `f` on the
circle and `epsilon>0`, uniform continuity supplies a depth `n` such that the
oscillation of `f` on each `J_{n,a}` is below `epsilon`. Replace `f` by a
step function taking one value on each such cylinder. The empirical and Haar
integrals each change by at most `epsilon`; their step-function integrals
differ by at most

\[
 \|f\|_\infty\,{2B_q\over S_q},                               \tag{8.1}
\]

which tends to zero by (7.7). Hence

\[
 \sigma_{s,S_q}\Rightarrow\lambda,                            \tag{8.2}
\]

where `lambda` is normalized Haar measure on `R/Z`.

For `0<r<=1/2`, translation invariance gives

\[
 (\lambda\times\lambda)\{(x,y):\operatorname{dist}(x,y)\leq r\}
 =2r.                                                         \tag{8.3}
\]

Indeed, for each fixed `x` the closed radius-`r` circle ball has Haar mass
`2r`; its two endpoints have Haar mass zero. Therefore (5.2) holds with

\[
 \alpha=1,\qquad C=2,\qquad r_0=1/2,\qquad M(q)=S_q,
 \qquad\nu=\lambda.                                           \tag{8.4}
\]

Proof-sketch conclusion: `C2_s` holds only for the artificial real `x_s`.
This is not canonical C2.

## 9. Complete splitting on the T14 triangle

We next verify the stronger coherent splitting predicate directly, without
applying a `pi` theorem by substitution. Fix `q`, a parent word `w` of length
`l`, and `a` in `D`, with `l+1<=m_q`. From (7.2),

\[
 C_s(S_q,w)\leq K_q10^{m_q-l}+B_q,                            \tag{9.1}
\]
\[
 C_s(S_q,wa)\geq K_q10^{m_q-l-1}.                            \tag{9.2}
\]

Since `K_q>=m_qB_q>=B_q`,

\[
 20C_s(S_q,wa)-C_s(S_q,w)
 \geq K_q10^{m_q-l}-B_q\geq0.                                \tag{9.3}
\]

Thus every one of the ten children has at least `1/20` of its parent's
count. Every parent is split at `eta=1/20`. Consequently the right side of
(6.3) is all of `E_s(l,S_q)`, so every such level is a splitting level for
`mu=1/2`.

Take the identity stage thinning

\[
 M(k)=S_k.                                                     \tag{9.4}
\]

It is strictly increasing and positive by T37. If `l<m<=k`, then
`l+1<=k<m_k=k+1`, so (9.3) applies in row `k`. Therefore

\[
 \operatorname{SplitCount}_s(m,S_k,1/2,1/20)=m
 \qquad(m\leq k).                                             \tag{9.5}
\]

Together with (8.2), an explicit witness for (6.6) is

\[
 \mu=1/2,\quad\eta=1/20,\quad d=1,\quad B=0,\quad
 m_0=k_0=0,\quad M(k)=S_k,\quad\nu=\lambda.                   \tag{9.6}
\]

The triangular inequality is equality:

\[
 dm-B=m=\operatorname{SplitCount}_s(m,M(k),\mu,\eta)
 \qquad(m\leq k).                                             \tag{9.7}
\]

This same displayed checkpoint family is already a positive existential
witness. More generally, even if only fixed-depth convergence had been
available, one would choose recursively a strictly increasing `q_k` beyond
the finitely many cutoffs needed for all `l<k`, and use `M(k)=S_{q_k}`.
Replacing the universal `M` in (6.7) by one poorly behaved family would reverse
the quantifiers and is invalid.

## 10. Moving-root mass and collision-energy share

Now set `m=m_q`, `S=10^m`, `B=B_q`, and `K=K_q`. From the definitions,

\[
 K=(R_q-2)m=(m^3(B+1)+1)m=m^4(B+1)+m,                        \tag{10.1}
\]

so, with `b=B/K`,

\[
 0\leq b\leq m^{-4}.                                         \tag{10.2}
\]

Let `z_q=0^m` be T37's moving all-zero root and let
`e_0=e_q(z_q)`. Its exact count and total sample size are

\[
 P_q=C_s(S_q,z_q)=K+e_0,\quad 0\leq e_0\leq B,\qquad
 S_q=SK+B.                                                     \tag{10.3}
\]

Its normalized mass `p_q=P_q/S_q` therefore satisfies

\[
 {1\over S+b}\leq p_q\leq {1+b\over S+b}
 \leq {1+m^{-4}\over10^m}.                                   \tag{10.4}
\]

In particular,

\[
 p_q\longrightarrow0,\qquad 10^m p_q\longrightarrow1.        \tag{10.5}
\]

At depth `m`, write `e_w=e_q(w)`. The exact unnormalized collision energy is

\[
 E_s(m,S_q)=\sum_{w\in D^m}(K+e_w)^2
 =SK^2+2KB+\sum_w e_w^2.                                     \tag{10.6}
\]

Because `0<=sum_w e_w^2<=B^2`, the fraction of collision energy carried by
the moving root,

\[
 \rho_q:={P_q^2\over E_s(m,S_q)},                              \tag{10.7}
\]

obeys

\[
 {1\over S+2b+b^2}\leq\rho_q
 \leq{(1+b)^2\over S+2b}
 \leq{(1+m^{-4})^2\over10^m}.                                \tag{10.8}
\]

Hence

\[
 \rho_q\longrightarrow0,\qquad 10^m\rho_q\longrightarrow1.  \tag{10.9}
\]

T37 separately machine-checks

\[
 0\leq\operatorname{normalizedStageLeakage}(q)\leq2/m^3
 \longrightarrow0,                                           \tag{10.10}
\]

where the denominator is the full energy in (10.6), and the leakage window
is the moving band of edge levels `[m,2m)`. Equation (10.10) is a global
statement over all `10^m` roots. Since the selected root has only
`rho_q` approximately `10^{-m}` of the energy, (10.10) does not imply small
leakage relative to that root. T37's local zero-path persistence instead comes
from its separate threshold `1-1/m`.

For the identity thinning (9.4), the T14 triangle tests absolute levels
`l<m'<=k`, while T37's moving root begins at `m_k=k+1`. The low-leakage window
is therefore beyond the whole tested triangle. Its root also has vanishing
global mass and energy share by (10.5) and (10.9). Neither fact negates the
existential coherent witness (9.6).

## 11. Imported no-original-branch theorem

T37's theorem

```text
DecimalFactorComplexity.ArtificialStreamObstruction.
  no_original_halfDominant_branch_explicit
```

is imported without reproof. In the notation here it states literally

\[
\neg\exists w\in D^{<\mathbb N}\ \exists a:\mathbb N\to D\
\ \forall i\ \exists Q\ \forall q\geq Q:\quad
 {1\over2}C_s(S_q,w\,a_{<i})\leq C_s(S_q,w\,a_{<i+1})
 \ \wedge\ 0<{1\over2}C_s(S_q,w\,a_{<i}).                    \tag{11.1}
\]

This excludes one fixed original-coordinate root and continuation that is
eventually half-dominant, with a row cutoff allowed to depend on depth `i`.
It does not exclude positive-density splitting, which asks for two substantial
children on enough collision-energy mass and does not choose a common branch.
The moving tangent uses roots `0^{m_q}` whose depths escape to infinity, so it
does not contradict (11.1).

## 12. Failure boundary

Proof-sketch conclusion: the artificial sibling realizes T37's checked moving-root tangent,
low-leakage windows, and no-fixed-original-branch conclusion. It does not
realize the full T14 failure package. The first failed literal is (6.7): the
specific admissible witnesses in (9.6) make its demanded strict inequality
impossible, because (9.7) is equality for every triangular entry. Clause
(6.10) is later and need not be used to locate the boundary.

This is an artificial-stream sibling conclusion only. It is no claim about
`pi`, canonical C2, canonical C1, or canonical A1.

BOUNDARY FAILS AT \(\forall\mu,\eta,d,B\in\mathbb R\ \forall m_0,k_0\in\mathbb N\ \forall M:\mathbb N\to\mathbb N\ \forall\nu\in\operatorname{Prob}(\mathbb R/\mathbb Z),\ [0<\mu<1\wedge0<\eta\leq1/10\wedge0<d\wedge0\leq B\wedge\operatorname{StrictMono}(M)\wedge(\forall k\in\mathbb N,0<M(k))\wedge\sigma_{s,M(k)}\Rightarrow\nu]\Longrightarrow\exists k\in\mathbb N,\ k_0\leq k\wedge\exists m\in\mathbb N,\ m_0\leq m\wedge m\leq k\wedge\operatorname{SplitCount}_s(m,M(k),\mu,\eta)<dm-B\)
