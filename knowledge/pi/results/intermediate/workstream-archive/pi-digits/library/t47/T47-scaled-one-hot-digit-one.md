# T47: a scaled one-hot family for forbidden digit 1

Claim status: `proof sketch` (rigorous prose, not machine-checked).

## 1. Provenance and exact scope

Canonical statement: `knowledge/pi/statements/pi-digits.txt`.

Canonical SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Original external source URL: none. The canonical statement is a
human-authored local root.

The canonical question asks whether every finite decimal word occurs
contiguously in the decimal expansion of pi. That question is open. This note
does **not** study the digits of pi. It studies only the structural sibling
given by T46's externally clocked base-16/base-10 residual system, with the
single forbidden decimal digit changed to `1`.

In particular, this note proves nothing about:

- `Real.pi` or any digit of pi;
- `T37.JMix Real.pi`;
- canonical V1 (decimal disjunctivity of pi);
- sibling V3 (every decimal digit recurring infinitely often in pi);
- arbitrary forbidden words;
- schedule-aware controllers that retain the external level as persistent
  state.

No finite computation is used. Every assertion below is symbolic and is
quantified over all family sizes.

## 2. Imported kernel-checked interfaces

Only the following accepted, kernel-checked interfaces are used as imported
premises. Their hashes were checked in the supplied knowledge library.

| Item | Module role used here | SHA-256 |
|---|---|---|
| T37 | exact cylinders, carries, and overlap bounds | `be14ac145519d4a9e9f394365ef4852ad8196e37f3ddb7ee682b31b0dd0459a6` |
| T43 | common-level external-clock continuation-language semantics | `b3658d1fb1f63e58f76d968658f57a9cc380fa3a830a4cbab9e8e7b0293298be` |
| T46 | the digit-parameterized concrete and residual systems, reachability, and induced packet acceptance | `b39e36c975ca9631531222da58d5d448e5a4641820e3d35428ebf2a8c22aad05` |

Names for the clock context, fixed-width words, rational states, packets, and
residuals occur in T46's public definitions through its imported types. No
separate result from an unverified note is assumed. The arithmetic claims
needed for the scaled family are re-derived below rather than inferred from
T46's theorem for its unchanged one-hot family.

## 3. Normalized target and quantifiers

T46's unchanged common-level family uses decimal values

\[
10^{1+j}\qquad (j\in\{0,\ldots,K\}),
\]

because its common family specializes the general parameter `r` to `r=1`.
For a fixed coefficient `c`, the exact scaled sibling therefore uses

\[
D^{(c)}_{K,j}=c\,10^{1+j}.
\]

The coefficient is chosen once, before `K`; it is not allowed to depend on
`K` or `j`. This note chooses the explicit coefficient

\[
\boxed{c=2}.
\]

The claim to be checked is:

> For every natural number `K`, including `K=0`, there is one external level
> `N_K` and a family indexed by `Fin (K+1)` of digit-1 reachable persistent
> residuals at level `N_K`. The residual map is injective. For every two
> distinct indices `u,v`, an explicitly defined continuation `w_u` follows
> the common schedule, is accepted from residual `u`, and is rejected from
> residual `v`.

Thus the family has exactly `K+1>K` members at one level. For `K=0`, the
reachability assertion is nonvacuous and pairwise separation is vacuous.

The external level and future schedule are shared test parameters in the
sense of T43/T46. They are not fields of the persistent residual state.

## 4. Exact scaled family

Fix `K : Nat` and put

\[
L=K+2,\qquad N=N_K=2L,
\qquad m=m_N=\operatorname{decimalLevel}(N).
\]

This is exactly T46's `familyLevel K = witnessLevel K 1`; only the decimal
values are scaled. Write the balanced context at level `N` as

\[
a=5^m,\qquad b=2^{4N-m}.
\]

For `j : Fin (K+1)`, set

\[
k_j=1+j,\qquad D_j=2\,10^{k_j}.
\]

For any level `n` and integer `0 <= D < 10^{m_n}`, define the rational state
`R(n,D)` by the same constructor used in T46:

\[
\begin{aligned}
m_n&=\operatorname{decimalLevel}(n),\\
A(n,D)&=\left\lfloor\frac{16^nD}{10^{m_n}}\right\rfloor,\\
R(n,D).\mathrm{level}&=n,\\
R(n,D).\mathrm{hexPrefix}&=\operatorname{fixedWord}_{16}(n,A(n,D)),\\
R(n,D).\mathrm{decimalPrefix}&=
  \operatorname{fixedWord}_{10}(m_n,D).
\end{aligned}
\]

Our concrete and persistent states are

\[
q_j=R(N,D_j),\qquad \rho_j=\operatorname{residualOf}(1,q_j).
\]

Replacing `D_j` by `10^{1+j}` gives T46's `familyState K j` and
`familyResidual K j`. Hence this is literally the requested scaling of the
T46 family, not a different indexing or level choice.

## 5. Preliminary bounds

**Step 1 (the decimal level is large enough).** Since `10 <= 16`,

\[
10^N\le 16^N.
\]

By the definition of `decimalLevel(N)=floor(log_10(16^N))`, this gives
`m >= N = 2L`.

Also `10^m <= 16^N=2^{4N}` and `2^m <= 10^m`, so `m <= 4N`.
Consequently the exponent in `b=2^{4N-m}` is an ordinary natural number.

**Step 2 (every scaled value fits below both required scales).** An index
`j : Fin (K+1)` satisfies

\[
k_j=1+j\le K+1=L-1.
\]

Therefore

\[
D_j=2\,10^{k_j}<10^{k_j+1}\le 10^L.
\]

As `L>0`, `10^L<25^L=5^{2L}`, and Step 1 gives

\[
D_j<10^L<5^{2L}\le5^m=a. \tag{5.1}
\]

In particular `D_j<a<10^m`, so every fixed-width word and rational state used
above is valid. This bound is uniform in `K` and `j`.

**Step 3 (shape of the decimal word).** The length-`m` base-10 word of
`D_j=2*10^{k_j}` consists of leading zeroes, one digit `2`, and exactly `k_j`
trailing zeroes. This follows directly from positional value and uniqueness
of a fixed-length base-10 expansion. Consequently the word, and every prefix
of it, contains only digits `0` and `2`; all of them avoid forbidden digit
`1`.

## 6. Common-level concrete reachability

We verify the hypotheses of T46's public
`reachableFor_of_all_prefixes_balanced` theorem for `d=1` and `q_j`.

**Step 4 (one rational point witnesses every prefix overlap).** Fix `j` and
put

\[
x_j=\frac{D_j}{10^m}\in[0,1).
\]

For `0 <= i <= N`, let `m_i=decimalLevel(i)`. The length-`i` hexadecimal
prefix of `q_j` has value

\[
A_i=\lfloor16^i x_j\rfloor,
\]

and its length-`m_i` decimal prefix has value

\[
E_i=\lfloor10^{m_i}x_j\rfloor.
\]

To see these identities without assuming a new lemma, take the corresponding
prefixes of the full fixed-width words. Their values are obtained by integer
division by `16^{N-i}` and `10^{m-m_i}`. The elementary identity

\[
\left\lfloor\frac{\lfloor y\rfloor}{q}\right\rfloor
=\left\lfloor\frac yq\right\rfloor\quad(q\in\mathbb N_{>0})
\]

gives the displayed formulas.

It follows from the defining property of floor that

\[
\frac{A_i}{16^i}\le x_j<\frac{A_i+1}{16^i},\qquad
\frac{E_i}{10^{m_i}}\le x_j<\frac{E_i+1}{10^{m_i}}. \tag{6.1}
\]

Thus `x_j` belongs to both half-open prefix cylinders. Their intersection is
nonempty. Equation (6.1) also gives validity of both numeric prefixes, and
their word lengths are the prescribed lengths by construction.

By Step 3, the decimal prefix avoids `1`. Hence every one of T46's
`BalancedFor 1` conjuncts holds for every scheduled prefix state of `q_j`:
the two length equalities, the two validity inequalities, digit-1 avoidance,
and nonempty cylinder intersection.

**Step 5 (reachability).** Applying
`T46.reachableFor_of_all_prefixes_balanced` to Step 4 gives

\[
\operatorname{ReachableFor}(1,q_j).
\]

Since `q_j.level=N`, this is exactly

\[
\operatorname{ReachableAtFor}(1,N,q_j). \tag{6.2}
\]

By the definition of T46's `PersistentReachableAt`, (6.2) and
`rho_j=residualOf(1,q_j)` imply

\[
\operatorname{PersistentReachableAt}(1,N,\rho_j). \tag{6.3}
\]

This proves common-level reachability for every `K` and every member of its
scaled family. Notice that T46's `SafeSupport` witness theorem was not used:
that theorem concerns the unchanged zero/one-supported words and cannot
establish reachability of the present zero/two-supported words.

## 7. Pairwise distinct initial residuals

**Step 6 (exact reduced carry).** At level `N`, cancellation of the common
factor `2^m` in `16^N/10^m` gives

\[
A(N,D_j)=\left\lfloor\frac{bD_j}{a}\right\rfloor.
\]

Unfolding T46's residual coordinate, or equivalently substituting in T37's
carry formula and dividing by that common factor, gives

\[
\kappa_j:=\rho_j.\mathrm{reducedCarry}
=a\left\lfloor\frac{bD_j}{a}\right\rfloor-bD_j
=-(bD_j\bmod a). \tag{7.1}
\]

The suffix coordinate is

\[
\rho_j.\mathrm{suffix}=D_j\bmod10=0, \tag{7.2}
\]

because `k_j>=1`.

**Step 7 (modular injectivity).** The number `a=5^m` is a power of `5` and
`b=2^{4N-m}` is a power of `2`, so `gcd(a,b)=1`. Suppose
`kappa_u=kappa_v`. Equation (7.1) then gives

\[
bD_u\equiv bD_v\pmod a.
\]

Cancellation of the invertible factor `b` gives `D_u congruent D_v (mod a)`.
Both values lie in `[0,a)` by (5.1), hence `D_u=D_v`. Therefore

\[
2\,10^{1+u}=2\,10^{1+v},
\]

so injectivity of powers of `10` gives `u=v`. Thus

\[
j\longmapsto\kappa_j
\quad\hbox{and hence}\quad
j\longmapsto\rho_j
\]

are injective. This is a symbolic argument for arbitrary `K`; no residue table
or bounded calculation is being extrapolated.

## 8. Explicit distinguishing continuation

Fix an oriented index `u : Fin (K+1)`. Let

\[
t=a=5^m>0,
\qquad S=\operatorname{incrementSum}(N,t),
\qquad x_u=\frac{D_u}{10^m}.
\]

For `h=0,...,t`, put

\[
n_h=N+h,\quad m_h=\operatorname{decimalLevel}(n_h),
\quad A_h=\lfloor16^{n_h}x_u\rfloor,
\quad E_h=\lfloor10^{m_h}x_u\rfloor.
\]

For `h<t`, define one packet `p_h` as follows:

- width `s_h=m_{h+1}-m_h`, which is the external schedule increment;
- hexadecimal digit `A_{h+1}-16A_h`, lying in `{0,...,15}`;
- the fixed-width `s_h`-digit decimal block of
  `E_{h+1}-10^{s_h}E_h`.

Finally define the oriented continuation explicitly by

\[
w_u=[p_0,p_1,\ldots,p_{t-1}]. \tag{8.1}
\]

More literally in the constructors embedded in T46, let

\[
q_f=R(N+t,D_u10^S).
\]

Then `w_u` is `packetsOfSymbols` applied to
`endpointContinuation q_f ... N t ...`, where the omitted proof fields are
the fixed-word length equalities established above and `N+t <= q_f.level`.
The displayed packet formula is the componentwise expansion of this exact
term; it is not merely an existential description of a path.

This is exactly T46/T43's endpoint-slicing construction with its endpoint
value changed from `10^{1+u}` to `2*10^{1+u}`. It has exactly `t` packets and
its widths are, by definition, the unique future schedule beginning at `N`.
Thus

\[
\operatorname{TailLegal}(N,w_u). \tag{8.2}
\]

**Step 8 (the oriented continuation is digit-1 legal).** At final level
`N+t`, the same rational point has decimal numerator

\[
D_u10^S=2\,10^{k_u+S}
\]

over denominator `10^{m+S}`. Its full decimal word again contains only zeroes
and one digit `2`; in fact every decimal packet in (8.1) is an all-zero block.
The fitting inequality follows by multiplying `D_u<10^m` by `10^S`.

For every prefix through level `N+t`, the argument of Step 4 applies to the
same point `x_u`. Therefore both prefix cylinders contain `x_u`, all numeric
prefixes are valid, and every decimal prefix avoids `1`. Every prefix state is
`BalancedFor 1`.

The prefix at level `N` is exactly `q_u`: its hexadecimal and decimal words
are determined by the same floors `floor(16^N x_u)` and
`floor(10^m x_u)=D_u`. Consequently T46's endpoint-continuation lemma makes
the concrete symbol path legal from `q_u`. T46's
`acceptedFor_packetsOfSymbols_of_legalFor` then gives

\[
\operatorname{AcceptedFor}
 (1,\operatorname{balancedContext}(N),1,\rho_u,w_u). \tag{8.3}
\]

## 9. Rejection from every other family member

Fix `v != u` and suppose, for contradiction, that the same continuation is
also accepted from `rho_v`.

**Step 9 (common final carry bounds).** Let `C_f` be the context after `w_u`,
and let `a_f,b_f` be its two scale coordinates. Let `X_u,X_v` be the final
reduced carries obtained from `rho_u,rho_v` respectively. T46's
`acceptedFor_final_bounds`, applied to the nonempty word `w_u`, gives

\[
-a_f<X_u<b_f,\qquad -a_f<X_v<b_f. \tag{9.1}
\]

Induction over the scheduled widths, using the balanced-context update at
each packet, gives the exact identity

\[
C_f=\operatorname{balancedContext}(N+t). \tag{9.1a}
\]

At every balanced level `n`, the defining inequalities

\[
10^{m_n}\le16^n<10^{m_n+1}
\]

and cancellation of `2^{m_n}` give `b_n<10a_n`. In particular
`b_f<10a_f`. Subtracting the two intervals in (9.1) therefore gives

\[
|X_u-X_v|<a_f+b_f<11a_f. \tag{9.2}
\]

**Step 10 (exact growth of a carry difference).** For a packet of decimal
width `s`, T46's displayed residual transition has the form

\[
\kappa'=(16\,5^s)\kappa+\text{an additive term depending only on the
context and packet}.
\]

When the same packet is applied to two residuals, the additive term cancels.
Induction over the `t` packets in `w_u` therefore gives

\[
X_u-X_v=16^tF(\kappa_u-\kappa_v), \tag{9.3}
\]

where

\[
F=\prod_{h<t}5^{s_h}=5^S>0.
\]

The context update multiplies its `a` coordinate by the same `5^{s_h}` at
each packet, so another direct induction gives

\[
a_f=Fa. \tag{9.4}
\]

Step 7 and `u != v` imply `kappa_u-kappa_v` is a nonzero integer, hence its
absolute value is at least `1`. Equations (9.3)-(9.4) and (9.2) imply

\[
16^tF\le|X_u-X_v|<11Fa.
\]

Cancelling the positive integer `F` yields

\[
16^t<11a. \tag{9.5}
\]

**Step 11 (the contradiction).** For every positive integer `z`,

\[
11z<16^z. \tag{9.6}
\]

Indeed, the case `z=1` is `11<16`. If (9.6) holds at `z>=1`, then
`11(z+1) <= 16*11z < 16^{z+1}`. This proves (9.6) by induction.

Here `t=a>0`, so (9.6) says `11a<16^t`, contradicting (9.5). The assumption
of acceptance from `rho_v` was false:

\[
\neg\operatorname{AcceptedFor}
 (1,\operatorname{balancedContext}(N),1,\rho_v,w_u). \tag{9.7}
\]

Together, (8.2), (8.3), and (9.7) make `w_u` an explicit one-sided
distinguishing continuation for every ordered pair `u != v`.

## 10. Continuation-language conclusion

By T46's definition,

\[
\operatorname{ContinuationLanguageAt}(1,N,1,\rho)
=\{w:\operatorname{TailLegal}(N,w)\ \text{and}\
       \operatorname{AcceptedFor}(1,C_N,1,\rho,w)\}.
\]

For `u != v`, equations (8.2)-(8.3) put `w_u` in the language of `rho_u`,
whereas (9.7) excludes it from the language of `rho_v`. Hence

\[
\neg\operatorname{RightLanguageEquivalentAt}(1,N,1,\rho_u,\rho_v). \tag{10.1}
\]

Combining (6.3), Step 7, and (10.1), for every `K : Nat` the map

\[
j:\operatorname{Fin}(K+1)\longmapsto\rho_j
\]

is injective, all its values are persistent-reachable at the one common level
`N_K=2(K+2)`, and all distinct values have distinct common-level right
languages. Since `card(Fin(K+1))=K+1>K`, this is an arbitrarily large
common-level reachable family for the explicit coefficient `c=2`.

Equivalently, this scaled family witnesses T46's structural
`InfiniteContinuationLanguageIndex (1 : Fin 10)` proposition. This final
sentence remains solely about the structural forbidden-digit-1 system; it has
no implication for pi, `JMix(pi)`, canonical V1, or sibling V3.

## 11. Obstruction audit

For `c=2`, none of the three possible obstructions occurs:

1. **Reachability:** no obstruction; all decimal prefixes use only `0` and
   `2`, and the represented rational point witnesses every cylinder overlap.
2. **Modular injectivity:** no obstruction; multiplication by the power of
   `2` called `b` is invertible modulo `a=5^m`, and all `D_j` lie in `[0,a)`.
3. **Continuation separation:** no obstruction; carry differences grow by
   `16^t` relative to the context's common power-of-`5` growth, contradicting
   simultaneous final acceptance when `t=a`.

The first failure of T46's **unchanged** coefficient-1 family is reachability,
because every such source word contains forbidden digit `1`. The scaled
coefficient `2` changes exactly that arithmetic feature while preserving the
one-place support and the separation mechanism.
