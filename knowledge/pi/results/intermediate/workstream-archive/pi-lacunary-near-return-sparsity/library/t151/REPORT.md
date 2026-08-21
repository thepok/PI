# T151: quantitative positive carry drift under all-n integrality

Status: `proof sketch`. Sections 2--8 give a self-contained proof of one
coefficient-model theorem. `verify_t151.py` is an exact-arithmetic
`experiment`; its finite checks test the implementation but are not the proof.
This is an A13/A14 sibling-model note. It makes no claim about fixed pi or any
named program conjecture.

```text
THEOREM_COUNT: 1
COMPARATOR_COUNT: 4
SCOPED_VERDICT_COUNT: 1
```

## 1. Provenance, normalization, and fixed target

The canonical source is the system-formulated local statement; no external
source URL was supplied. The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks, for fixed pi and base 10, whether

```text
for every A >= 1 there exists n0 >= 1 such that
for every n >= n0 there exists N >= 1 with
A*n*Q_pi(n,N) <= N^2,
```

for strict circle distance and ordered, diagonal-inclusive pairs. Nothing here
addresses those quantifiers.

Fix instead:

1. a prime `p`;
2. nonempty finite lists `a=(a_1,...,a_r)` and `b=(b_1,...,b_s)` of positive
   integers, with repetitions retained;
3. balance `sum_i a_i=sum_j b_j`;
4. unequal coefficient multisets;
5. the all-n integrality hypothesis

\[
 R(n)={\prod_i(a_i n)!\over\prod_j(b_j n)!}\in\mathbb Z
 \qquad\hbox{for every integer }n\ge0.                     \tag{1.1}
\]

Put

\[
 M=\max(\{a_i\}_i\cup\{b_j\}_j),\qquad
 \Lambda(x)=\sum_i\lfloor a_i x\rfloor-
             \sum_j\lfloor b_j x\rfloor.                  \tag{1.2}
\]

An **atom** is an open component of `[0,1]` after removing all discontinuities
`m/c` of the floors in (1.2); `Lambda(I)` denotes its constant value. For a
positive atom `I`, define, before any computation,

\[
 d_p(I)=\min\left\{d\ge1:\exists k\in\{1,\ldots,p^d-2\},
                   {k\over p^d-1}\in I\right\}.             \tag{1.3}
\]

Section 7 proves this set is nonempty. Let

\[
 d=d_p(I),\quad h_I=\Lambda(I)>0,\quad
 H=\lceil\log_p M\rceil:=\min\{h\ge0:p^h\ge M\},           \tag{1.4}
\]

and fix the explicit access and zero-flush lengths

\[
 T_{\rm acc}=d+H,\qquad T_{\rm flush}=H.                   \tag{1.5}
\]

The fixed quantitative target is

\[
 \boxed{\mu_+(p;a,b)\ge{(p-1)h_I\over d}>0.}               \tag{Q151}
\]

Here `mu_+` is the maximum edge-weight mean of an accessible nonempty closed
walk in the raw carry graph below. The graph is finite, so this maximum exists.
The proof also gives the access/flush-visible certificate

\[
 \mu_+\ge{(p-1)h_I\over T_{\rm acc}+d+T_{\rm flush}}
         ={(p-1)h_I\over2d+2H}.                            \tag{1.6}
\]

Ambiguities fixed: input is LSDF; digit-labeled parallel edges are retained;
only states reachable from the zero state are accessible; terminal weights are
charged on finite words but not cycles; cycle units are `(p-1)*v_p`; and
integrality in (1.1) is universal, not a bounded test.

## 2. All-n integrality forces Landau nonnegativity

Counting multiples of powers of a prime `q` gives

\[
 v_q(m!)=\sum_{e\ge1}\left\lfloor{m\over q^e}\right\rfloor,
\quad
 v_q(R(n))=\sum_{e\ge1}\Lambda(n/q^e).                     \tag{2.1}
\]

Balance makes `Lambda` one-periodic. Suppose `Lambda(x_0)<0`. Reduce modulo one
to `x_0 in [0,1)`. Since a finite sum of floor functions is right-continuous
with finitely many jumps, `Lambda` is negative on a nonempty right interval
`J subset [0,1)`. Choose a prime

\[
 q>M                                                             \tag{2.2}
\]

large enough that some `n/q` with `0<=n<q` lies in `J`. This is possible by
Euclid's theorem and mesh refinement. For every `e>=2`,

\[
 0\le n/q^e<1/q<1/M,                                       \tag{2.3}
\]

so all floors defining `Lambda(n/q^e)` vanish. Equation (2.1) yields
`v_q(R(n))=Lambda(n/q)<0`, impossible for the positive integer (1.1). Hence

\[
 \boxed{\Lambda(x)\ge0\quad\hbox{for every real }x.}        \tag{2.4}
\]

This is proved here and is not imported from any prior note.

## 3. Unequal multisets produce a positive atom

Let

\[
 m_c=\#\{i:a_i=c\}-\#\{j:b_j=c\}.                          \tag{3.1}
\]

If the multisets differ, choose the largest `C` with `m_C!=0`. At `x=1/C`,
the jump of `floor(Cx)` is one, every term with smaller coefficient has no
jump there, and every larger coefficient has signed multiplicity zero.
Therefore the jump of `Lambda` is `m_C!=0`; `Lambda` is not identically zero.
Together with (2.4), it is positive somewhere. Right-continuity and finite
jump count then give at least one positive open atom `I`, with integer height

\[
 h_I=\Lambda(I)\ge1.                                      \tag{3.2}
\]

## 4. Independently reconstructed base-p carry graph

For a coefficient `c`, its carry set is

\[
 K_c=\{0,1,\ldots,c-1\}.                                   \tag{4.1}
\]

Indeed, for `0<=gamma<c` and `0<=e<p`,
`0<=floor((ce+gamma)/p)<c`. The complete raw state space is

\[
 K=\prod_i K_{a_i}\times\prod_j K_{b_j}.                   \tag{4.2}
\]

Write `q=(alpha_1,...,alpha_r;beta_1,...,beta_s)` and let `q_0` be all zero.
For every digit `e in {0,...,p-1}`, retain one labeled edge `q --e/w--> q'`,
where

\[
 \alpha'_i=\left\lfloor{a_i e+\alpha_i\over p}\right\rfloor,
 \qquad
 \beta'_j=\left\lfloor{b_j e+\beta_j\over p}\right\rfloor. \tag{4.3}
\]

The emitted digit for coefficient `c` and carry `gamma` is

\[
 \rho_c(\gamma,e)=ce+\gamma-p\left\lfloor{ce+\gamma\over p}\right\rfloor.
                                                                    \tag{4.4}
\]

Define edge and terminal weights

\[
 w(q,e)=\sum_j\rho_{b_j}(\beta_j,e)-
        \sum_i\rho_{a_i}(\alpha_i,e),
\quad
 \tau(q)=\sum_j s_p(\beta_j)-\sum_i s_p(\alpha_i).         \tag{4.5}
\]

If a length-`t` LSDF word represents `n=sum_(u<t)e_u p^u`, induction in
(4.3) gives the exact state

\[
 \boxed{\alpha_i=\lfloor a_i n/p^t\rfloor,\qquad
        \beta_j=\lfloor b_j n/p^t\rfloor.}                 \tag{4.6}
\]

Thus (4.6), as `t>=0` and `0<=n<p^t` vary, characterizes accessibility. The
low output digits in (4.4), followed by the digit sums of the unflushed carries,
give

\[
 \sum_{u<t}w(q_u,e_u)+\tau(q_t)
 =\sum_j s_p(b_jn)-\sum_i s_p(a_in).                        \tag{4.7}
\]

Legendre's digit identity `(p-1)v_p(m!)=m-s_p(m)` and balance yield

\[
 \boxed{\sum_{u<t}w(q_u,e_u)+\tau(q_t)
       =(p-1)v_p(R(n)).}                                   \tag{4.8}
\]

This specifies and verifies the entire graph, including terminal carries.

## 5. Landau potential and cycle identity

Define

\[
 \Phi(q)=\sum_i\alpha_i-\sum_j\beta_j.                     \tag{5.1}
\]

For the accessible state (4.6), direct substitution gives

\[
 \boxed{\Phi(q)=\Lambda(n/p^t)\ge0.}                       \tag{5.2}
\]

Expanding (4.5), balance cancels every term linear in the input digit:

\[
 \boxed{w(q,e)=p\Phi(q')-\Phi(q).}                          \tag{5.3}
\]

For any accessible nonempty closed walk
`C=(q_0,q_1,...,q_l=q_0)`, cyclic reindexing gives

\[
 \boxed{W(C)=(p-1)\sum_{u=0}^{l-1}\Phi(q_u).}              \tag{5.4}
\]

All terms are nonnegative by (5.2). In particular every accessible cycle has
nonnegative weight. Every closed walk decomposes into simple directed cycles,
and its mean is their length-weighted average, so `mu_+` may be computed over
the finite set of accessible simple cycles.

## 6. Periodic state, access, and zero flush

Let `d>=1`, `P=p^d`, `Q=P-1`, and choose

\[
 x={k\over Q}\in(0,1),\qquad 1\le k\le Q-1.                \tag{6.1}
\]

Write `k=sum_(u<d)z_u p^u`, with exactly `d` padded LSDF digits. Define

\[
 q_x=(\lfloor a_i x\rfloor_i;\lfloor b_jx\rfloor_j).       \tag{6.2}
\]

After the block `z_0,...,z_(d-1)`, a coefficient-`c` carry `gamma` becomes
`floor((ck+gamma)/P)`. For `gamma=floor(ck/Q)`,

\[
 \gamma Q\le ck<(\gamma+1)Q
 \quad\Longrightarrow\quad
 \gamma P\le ck+\gamma<(\gamma+1)P.                        \tag{6.3}
\]

Thus the block fixes every carry in (6.2), producing a length-`d` closed walk
`C_x` at `q_x`.

Now take `H` from (1.4), `T=d+H`, and

\[
 A=\lceil p^T x\rceil.                                    \tag{6.4}
\]

First, `A<p^T`: otherwise `0<1-x<1/p^T`, while
`1-x=(Q-k)/Q>=1/Q>1/p^T`. Next,

\[
 0\le A/p^T-x<1/p^T\le1/(PM)<1/(QM).                       \tag{6.5}
\]

For each `c<=M`, the distance from `cx=ck/Q` to the next strictly larger
integer is a positive multiple of `1/Q`, hence at least `1/Q`. Equation (6.5)
therefore gives `floor(cA/p^T)=floor(cx)`. By (4.6), the `T` LSDF digits of
`A` access `q_x`. This proves the fixed bound

\[
 \boxed{T_{\rm acc}=d+H.}                                  \tag{6.6}
\]

On input zero every carry obeys `gamma -> floor(gamma/p)`. Since
`0<=gamma<c<=M<=p^H`, after at most `H` zeros every carry is zero:

\[
 \boxed{T_{\rm flush}=H.}                                  \tag{6.7}
\]

Neither bound is asserted minimal.

## 7. Existence and coefficient-explicit bound for d_p(I)

Every atom endpoint is a reduced fraction with denominator at most `M`. If
`u/v<r/s` are consecutive distinct endpoints, then

\[
 |I|={r\over s}-{u\over v}={rv-us\over sv}\ge{1\over sv}
 \ge{1\over M^2}.                                         \tag{7.1}
\]

Define the coefficient-explicit number

\[
 D_p(M)=\min\{e\ge1:p^e-1>M^2\}.                           \tag{7.2}
\]

The grid spacing `1/(p^D-1)` is then strictly smaller than `|I|`. Every open
interval of length greater than this spacing contains a grid point strictly in
its interior. Because `I subset (0,1)`, that point is `k/(p^D-1)` with
`1<=k<=p^D-2`. Hence (1.3) is nonempty and

\[
 \boxed{d_p(I)\le D_p(M).}                                 \tag{7.3}
\]

This proof explains the strict inequality in (7.2); equality of interval
length and grid spacing would not force an interior grid point.

## 8. Proof of the fixed quantitative inequality

Take the witness `x=k/(p^d-1)` in the positive atom `I`. Its state `q_x` is
accessible by (6.6), and

\[
 \Phi(q_x)=\Lambda(x)=h_I.                                 \tag{8.1}
\]

Every other state on the period cycle `C_x` is accessible and therefore has
nonnegative potential by (5.2). The cycle identity (5.4) gives

\[
 W(C_x)=(p-1)\sum_{q\in C_x}^{\rm time}\Phi(q)
        \ge(p-1)h_I.                                      \tag{8.2}
\]

Since `C_x` has length `d`,

\[
 \mu_+\ge {W(C_x)\over d}\ge{(p-1)h_I\over d}>0,           \tag{8.3}
\]

which is exactly (Q151).

For the requested explicit access/flush accounting, concatenate: the
length-`T_acc` access path, one period `C_x`, and the length-`T_flush` zero
path. This is a closed walk at the zero state. It visits `q_x`, all its
potentials are nonnegative, and its length is `2d+2H`; thus its mean is at
least (1.6). Decomposing it into simple cycles is another direct certificate
that some accessible cycle has at least that mean.

Finally, `h_I>=1` and (7.3) turn (8.3) into the coefficient-only corollary

\[
 \boxed{\mu_+(p;a,b)\ge {p-1\over D_p(M)}>0.}               \tag{8.4}
\]

The direction in (8.4) is valid because `d<=D_p(M)`.

## 9. Exact finite-length valuation family

The access construction also exposes exact integers, not merely an asymptotic
claim. Let `z` denote the period block of value `k`, let the access word have
value `A` and length `T`, and for `m>=0` set

\[
 N_m=A+p^T k{p^{dm}-1\over p^d-1}.                          \tag{9.1}
\]

The LSDF word is the access word followed by `m` copies of `z`; its endpoint
is `q_x`. Comparing (4.8) for `m` and for zero copies gives

\[
 \boxed{(p-1)v_p(R(N_m))=(p-1)v_p(R(A))+mW(C_x).}           \tag{9.2}
\]

Thus (8.2) yields the exact lower bound

\[
 v_p(R(N_m))\ge v_p(R(A))+m h_I.                            \tag{9.3}
\]

Appending `H` zero digits leaves `N_m` unchanged and flushes all terminal
carries. Equations (9.1)--(9.3) are exact integral-family statements under
(1.1), not a counterfamily.

## 10. Convention check and experiment target

Use the integral multinomial ratio

\[
 R(n)={(3n)!\over(n!)^3},\qquad p=2.
                                                                    \tag{10.1}
\]

It is integral for every `n` because it is a multinomial coefficient. Here
`a=(3)`, `b=(1,1,1)`, `M=3`, and on `[0,1)`

\[
 \Lambda(x)=\lfloor3x\rfloor,
\tag{10.2}
\]

with positive atoms `(1/3,2/3)` of height 1 and `(2/3,1)` of height 2. For
`I=(1/3,2/3)`, depth 2 meets only its endpoints, while `x=3/7` is interior;
thus `d_2(I)=3`. Also `H=2`, so the fixed constants are `T_acc=5` and
`T_flush=2`. The period block has LSDF digits `1,1,0`, fixes the
multiplier-three carry `1`, and has starting potentials `(1,2,2)`, hence
weight 5 and mean `5/3`. In particular (Q151) gives the valid lower bound

\[
 \mu_+\ge {1\over3}.                                      \tag{10.3}
\]

The graph also contains the digit-one loop at carry 2, of weight and mean 2,
so this atom bound need not equal either the selected period mean or `mu_+`.

`verify_t151.py` reconstructs this example and a bounded census of integral
multinomial ratios `a=(sum b_j)`, for primes 2, 3, and 5. It verifies the fixed
inequality, access and flush formulas, carry identities, and exact families
using rational and integer arithmetic. Every such finite check is an
`experiment`, never evidence for the universal theorem.

## 11. Comparison with T141, T143, T145, and T148

The four byte-pinned comparator reports are unverified notes and are used only
to mark overlap. No claim from them is a premise.

| Item and delivered SHA-256 | What the note argues (unverified) | T151 boundary |
|---|---|---|
| T141, `e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356` | A general multiplication-carry graph, tropical extrema, cycle asymptotics, and a central-trinomial example. | Motivation only. T151 independently derives the raw graph and adds a fixed atom-wise quantitative lower bound with explicit `d`, access, flush, and coefficient-only constants. |
| T143, `b446b83025fd408fdbc8580e0e6871ab514ad169b0fe1d33407f6ad9061ca0d9` | Terminal-normalized residual equivalence, quotienting, and cycle-mean preservation for finite weighted transducers. | T151 does not quotient. The quantitative certificate is exhibited directly in the raw coefficient graph, so no residual-equivalence claim is used. |
| T145, `17774f8020ddba63203d2a956e1edbd3e2d432a32cafde11386d35a3514d229c` | Under all-n integrality, Landau potentials are nonnegative and unequal multisets yield some positive accessible cycle. | T151 re-proves those ingredients, fixes a positive atom before computation, and upgrades qualitative positivity to `(p-1)h_I/d_p(I)` and `(p-1)/D_p(M)`, with `T_acc=d+H` and `T_flush=H`. This is the intended scoped extension, not an import. |
| T148, `7a360dfc73ae9aa7c4582bc18f93cc06b7317f8fc1226b54fa0c11ca5fc223d7` | Without all-n integrality, a positive atom can lie on a periodic orbit with negative total; its displayed ratio has `R(1)=3/4`. | Its counterfamily is outside T151's explicit domain. Section 2 proves that T151 integrality rules out every negative orbit potential, exactly blocking periodic-orbit sign loss. T151 does not contradict or reuse its counterfamily proof. |

The duplication boundary is explicit: Sections 2--5 necessarily overlap the
subject of T145 but are independently supplied because sketches cannot be
premises. T151's scoped addition is the quantitative atom-period theorem,
coefficient-only `D_p(M)` bound, and complete access/flush accounting.

## 12. Transfer firewall

Every transfer premise toward the machine-checked T7 finite-cylinder interface
or the machine-checked T107 triangular Fourier interface remains **unproved**.
In particular, nothing here supplies:

1. an exact representation of pi by these factorial ratios;
2. complete reduction and cancellation control for its numerator and modulus;
3. the decimal powers-of-2 and powers-of-5 transient;
4. multiplicative order of 10 modulo a surviving coprime modulus;
5. truncation error uniform under all relevant `10^i-10^j`;
6. ordered, diagonal-inclusive metric or cylinder occupancy for T7;
7. coherent boundary and collected Fourier budgets for T107.

Prime-adic cycle drift proves none of these. No transfer premise is asserted,
and no implication toward the canonical question is claimed.

## 13. Self-contained replay

In a directory containing only the delivered files, run

```bash
python3 verify_t151.py
sha256sum -c SHA256SUMS
```

The script hash-checks the canonical statement and all four comparators. It
then reconstructs exact atoms, `d_p(I)`, `D_p(M)`, carry states, labeled edges,
terminal weights, access words, period cycles, flush paths, and valuation
families for the displayed model and a bounded multinomial census. Its output
is captured in `raw_output.txt`. All checks are labeled `experiment`.

## 14. Sole scoped verdict

SCOPED_VERDICT: DEVELOP QUANTITATIVE RELATED-MODEL PROOF SKETCH
