# T11: almost-everywhere stress test of T8

Status: `proof sketch` (rigorous prose, not machine-checked).

## 1. Artifact scope and claim boundary

This markdown note is the only claim-bearing T11 artifact. The files ending in
`_SOURCE.txt` are byte-exact source snapshots used only to check definitions,
theorem statements, and line locators. They are not submitted as a T11 Lean
formalization, and T11 claims no Lean theorem.

The immutable canonical statement is retained as `CANONICAL_STATEMENT.txt`.
Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical conjecture C1 concerns the single fixed number `pi` and has the
quantifier order

\[
 \forall s\in(0,1)\ \exists C_s\ge 1\ \forall m,N\ge 1,
 \qquad
 R_\pi(m,N)\le C_s\bigl(N+N^2 10^{-sm}\bigr).              \tag{1.1}
\]

The pairs counted by `R_pi` are ordered and satisfy the weak cutoff
`|a-b| >= m`. This note does not decide (1.1). It establishes only:

1. an **almost-everywhere sibling** verdict for the result of replacing T8's
   orbit point `pi` by a Lebesgue-random real `alpha`; and
2. a **conditional reduction** from one explicit scale-dependent spectral
   premise, plus T8/T2's effective-irrationality premise, to the exact
   right-hand side in (1.1).

Nothing below is specialized from an almost-everywhere set to `alpha=pi`.
No spectral estimate is asserted for `pi`, and no conclusion that C1 holds or
fails for `pi` is drawn. The scale-dependent premise in Section 6 is called
sufficient, not optimal or weakest.

### Quantifiers and conventions fixed in advance

1. `Q0` is an arbitrary natural number fixed before T8's scale variables.
2. `m,N` are positive integers. At `m=1`, T8 uses exactly the inclusive
   frequency range `h=1,...,10`.
3. All orbit exponents in this note are `a=0,...,N-1`. Philipp uses
   `k=1,...,N`; the matching sequence is therefore `n_k=h*10^(k-1)`.
4. Exceptional null sets may depend on `h`. A finite intersection handles all
   ten T8 frequencies simultaneously.
5. The almost-everywhere conclusion will use one full-measure set on which the
   failure holds for every natural `Q0`; no uncountable-intersection argument
   is involved.
6. In Section 6, `A_s` may depend on `s` but is chosen before, and is
   independent of, `m,N`.

## 2. Exact source pins and locators

Run `sh verify_sources.sh` beside these artifacts to check every hash below.

### 2.1 T8 source

Retained citation snapshot: `T8_SPECTRAL_SOURCE.txt`.

```text
SHA-256 f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9
```

This is byte-identical to the machine-checked T8 source indexed in the
knowledge library. Exact locators in the retained snapshot are:

- lines 37-42: `decimalFrequency m = 10^m` and `halfFrequency`;
- lines 44-57: the Boolean-oriented `(lag,start)` representation and its two
  ordered coordinates;
- lines 59-68: `orderedLongPairDomain`;
- lines 70-94: `mem_orderedLongPairDomain_iff` with every endpoint;
- lines 96-123: the fixed orbit phase and exponential sum;
- lines 154-178: the positive energy and the order `exists K, forall m,N`;
- lines 241-289: `|Q| <= 2N^2`;
- lines 541-551: the Fejer-majorant estimate used in Section 6; and
- lines 598-648: the Cauchy-Schwarz mechanism.

The source is retained to fix T8 exactly, not as evidence that its spectral
hypothesis holds.

### 2.2 Arithmetic exclusion definition

Retained citation snapshot: `T25_ARITHMETIC_EXCLUSION_SOURCE.txt`.

```text
SHA-256 86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c
```

This source is included only because T8's domain imports its definitions.
Lines 28-29 define

\[
 d(n,r)=10^n(10^r-1),                                      \tag{2.1}
\]

and lines 48-56 define, with natural values cast to reals in the inequality,

\[
 \operatorname{ArithmeticExcluded}(\mu,c,Q_0,m,n,r)
 \iff Q_0\le d(n,r)\ \mathbin{\land}\
 10^{-m}\le d(n,r)\frac{c}{d(n,r)^\mu}.                   \tag{2.2}
\]

No theorem from this T25 file is presented as the T11 deliverable.

### 2.3 T2 comparator

Retained citation snapshot: `T2_RESIDUAL_BRIDGE_SOURCE.txt`.

```text
SHA-256 ffe231e2750445a8f2c0a342cb60e1259a2427e5bb0f8067bf1350ab62bdeba3
```

This is byte-identical to the machine-checked T2 source indexed in the
knowledge library. Lines 27-37 define its residual-decay predicate, including
the effective-irrationality premise and the order
`forall s, exists C_s, forall m,N`. Lines 142-150 compare the canonical
ordered count to the residual count, and lines 152-166 transfer the residual
bound to C1 with the same `C_s`.

### 2.4 Lacunary LIL

Walter Philipp, *Limit theorems for lacunary series and uniform distribution
mod 1*, Acta Arithmetica 26 (1975), 241-251,
DOI <https://doi.org/10.4064/aa-26-3-241-251>.

Publisher PDF URL:
<https://www.impan.pl/shop/publication/transaction/download/product/100600?download.pdf>.

Retained file: `philipp-1975-lacunary.pdf`.

```text
SHA-256 4d0edc8170fe1ddf368ada0fd64ed7ec48411840ab6c07fdd658e44fbae84e3a
```

The PDF is a two-up image scan without a usable text layer. The assertions
below were checked visually, not accepted from OCR. Exact visual locators are:

- PDF page 1, right half, journal page 241, formula (1.2): a lacunary sequence
  satisfies `n_(k+1)/n_k >= q > 1` for `k=1,2,...`;
- PDF page 2, left half, journal page 242, formula (1.8) and the sentence
  immediately below it: for any lacunary sequence `(n_k)`, not necessarily
  integer-valued,

\[
 \limsup_{N\to\infty}
 \frac{\left|\sum_{k=1}^{N}\exp(2\pi i n_k x)\right|}
      {\sqrt{N\log\log N}}=1
 \quad\text{for almost every }x.                           \tag{2.3}
\]

Philipp attributes the upper bound to Salem-Zygmund and the matching lower
bound to Erdos-Gaal. Thus Philipp is pinned here as a secondary source for the
complete equality at (1.8), not claimed as the original source.

## 3. Exact T8 domain at `(mu,c,m)=(8,1,1)`

Fix `Q0 in N` and `N>=1`. A T8 domain record consists of an orientation
`epsilon in {false,true}` and a core `(r,n)`. By the machine-checked membership
equivalence at T8 lines 70-94, membership at `m=1` is exactly

\[
 0<r,\qquad 1\le r,\qquad r<N,\qquad n<N-r,\qquad
 \neg\operatorname{ArithmeticExcluded}(8,1,Q_0,1,n,r).    \tag{3.1}
\]

The first inequality is redundant. For such `r,n`, set

\[
 d=10^n(10^r-1).
\]

Since `r>=1`, `10^r-1>=9`; since `10^n>=1`,

\[
 d\ge9>0.                                                   \tag{3.2}
\]

At `(mu,c,m)=(8,1,1)`, the second conjunct in (2.2) would be

\[
 \frac1{10}\le d\frac1{d^8}=\frac1{d^7}.                 \tag{3.3}
\]

But `d>=9` gives `d^7>=9^7>10`, hence `1/d^7<1/10`.
Consequently (3.3) is false, regardless of whether the first conjunct
`Q0<=d` holds. Thus the exclusion is false for every `Q0`.

T8 maps the `false` orientation to `(a,b)=(n,n+r)` and the `true` orientation
to `(a,b)=(n+r,n)`. Condition `n<N-r` is equivalent to `n+r<N`. Conversely,
every ordered unequal pair `0<=a,b<N` has the unique data

\[
 n=\min(a,b),\qquad r=|a-b|\ge1,
\]

and its order uniquely determines the Boolean orientation. Therefore the T8
coordinate map is a bijection

\[
 Q(8,1,Q_0,1,N)\ \longleftrightarrow\
 \{(a,b):0\le a,b<N,\ a\ne b\}.                           \tag{3.4}
\]

This includes `N=1`, when both sides are empty, and gives
`|Q(8,1,Q0,1,N)|=N(N-1)`. Thus the T9 lead is true. This proof uses the exact
definitions above and does not use the unverified T9 note as a premise.

## 4. Exact spectral identity for the alpha sibling

T8's `orderedPhaseArgument` contains the fixed orbit point `Real.pi`; its
general phase function also contains the universal circle constant `2*pi`.
Define the **alpha sibling** by replacing only that orbit point by a real
`alpha`, leaving the phase convention unchanged. Write

\[
 e(x)=\exp(2\pi i x),\qquad
 Z_h(N;\alpha)=\sum_{a=0}^{N-1}e(h10^a\alpha),             \tag{4.1}
\]

and, using (3.4),

\[
 S_h(1,N;\alpha)=
 \sum_{\substack{0\le a,b<N\\a\ne b}}
 e\bigl(h(10^a-10^b)\alpha\bigr).                        \tag{4.2}
\]

The sum in (4.2) is over ordered pairs. Since

\[
 e\bigl(h(10^a-10^b)\alpha\bigr)
 =e(h10^a\alpha)\,\overline{e(h10^b\alpha)},              \tag{4.3}
\]

direct expansion gives

\[
 |Z_h(N;\alpha)|^2
 =\sum_{a=0}^{N-1}\sum_{b=0}^{N-1}
   e\bigl(h(10^a-10^b)\alpha\bigr).                       \tag{4.4}
\]

There are exactly `N` diagonal terms `a=b`, each equal to one. Removing them
leaves exactly (4.2), with both orientations retained. Hence

\[
 \boxed{
 S_h(1,N;\alpha)=
 \left|\sum_{a=0}^{N-1}\exp(2\pi i h10^a\alpha)\right|^2-N.}
                                                                    \tag{4.5}
\]

The right side is real, so no conjugation or factor two is missing.

## 5. Full LIL specialization and almost-everywhere verdict

For each T8 frequency `h in {1,...,10}`, put

\[
 n_k^{(h)}=h10^{k-1},\qquad k=1,2,\ldots .                 \tag{5.1}
\]

Every term is positive and integer-valued, and for every `k>=1`,

\[
 \frac{n_{k+1}^{(h)}}{n_k^{(h)}}=10.                       \tag{5.2}
\]

Thus Philipp's complete gap hypothesis (1.2) holds with the same `q=10>1`
for every one of the ten sequences. The first `N` source terms are exactly
`h10^a` for `a=0,...,N-1`; there is no index shift left over. Formula (2.3)
therefore gives, for each fixed `h`,

\[
 \limsup_{N\to\infty}
 \frac{|Z_h(N;\alpha)|}{\sqrt{N\log\log N}}=1             \tag{5.3}
\]

for Lebesgue-almost every `alpha in [0,1)`. Let `Omega_h` be a full-measure
set for (5.3). The finite intersection

\[
 \Omega=\bigcap_{h=1}^{10}\Omega_h                        \tag{5.4}
\]

still has full measure. All sums are one-periodic in `alpha`, so the union of
the integer translates of `Omega` has full Lebesgue measure in `R`. This
verifies the source theorem simultaneously for all T8 frequencies before any
frequency is selected.

Define the alpha-sibling of T8's `m=1` positive spectral energy by

\[
 E_\alpha(1,N)=\sum_{h=1}^{10}|S_h(1,N;\alpha)|^2.          \tag{5.5}
\]

Fix `alpha in Omega`. Retain only the nonnegative `h=1` summand. Equation
(5.3) implies that there are arbitrarily large `N` such that

\[
 |Z_1(N;\alpha)|\ge\tfrac12\sqrt{N\log\log N}.             \tag{5.6}
\]

Along those `N`, once `log log N>=8`, (4.5) gives

\[
 S_1(1,N;\alpha)
 \ge N\left(\tfrac14\log\log N-1\right)
 \ge \tfrac18N\log\log N.                               \tag{5.7}
\]

Consequently, along an unbounded sequence,

\[
 \frac{E_\alpha(1,N)}{10N^2}
 \ge\frac{|S_1(1,N;\alpha)|^2}{10N^2}
 \ge\frac{(\log\log N)^2}{640}\longrightarrow\infty.    \tag{5.8}
\]

The exact failure quantifiers are therefore

\[
 \boxed{
 \text{for Lebesgue-a.e. }\alpha,\quad
 \forall Q_0\in\mathbb N\ \forall K\ge0\ \exists N\ge1,
 \quad E_\alpha(1,N)>K\,10N^2.}                          \tag{5.9}
\]

The same full-measure set works for every `Q0` because Section 3 removed
`Q0` from the `m=1` domain identically; no intersection over `Q0` is needed.
Since T8's alpha-sibling uniform condition is

\[
 \exists K\ge0\ \forall m,N\ge1,
 \quad E_\alpha(m,N)\le K10^mN^2,                         \tag{5.10}
\]

the witness scale `m=1` in (5.9) proves the following **almost-everywhere
sibling** verdict: for Lebesgue-almost every real `alpha`, and for every
natural `Q0`, T8's normalized uniform energy bound fails.

This does not imply failure at `alpha=pi`; a full-measure set need not contain
any specified real. It also does not imply that C1 fails for `pi`.

## 6. One scale-dependent sufficient condition

This section is a **conditional reduction**. Return to T8's fixed-`pi`
definitions with arbitrary but fixed arithmetic parameters `(mu,c,Q0)`. For
positive `m,N`, put

\[
 H=10^m,\qquad
 E(m,N)=\sum_{h=1}^{H}|S_h(m,N)|^2,\qquad
 T_s(m,N)=N+N^2H^{-s}.                                    \tag{6.1}
\]

Consider the following premise: for every real `s` with `0<s<1`, there is a
real `A_s>=0`, chosen before `m,N`, such that for all positive integers `m,N`,

\[
 \boxed{E(m,N)\le A_s H\,T_s(m,N)^2.}                     \tag{6.2}
\]

This is one explicit sufficient condition. It is not asserted for `pi` or for
almost every `alpha`, and it is not called optimal or weakest.

The machine-checked T8 Fejer estimate at lines 541-551 is

\[
 R_{\rm res}(m,N)
 \le \frac{\pi^2}{2H}|Q(m,N)|
     +\frac{\pi^2}{H}\sum_{h=1}^{H}|S_h(m,N)|.             \tag{6.3}
\]

T8's cardinality theorem gives `|Q(m,N)|<=2N^2`. The inclusive integer range
`1<=h<=H` has exactly `H` members. Cauchy-Schwarz and (6.2) therefore give

\[
 \sum_{h=1}^{H}|S_h|
 \le\sqrt{H E(m,N)}
 \le\sqrt{H\,A_sH\,T_s(m,N)^2}
 =\sqrt{A_s}\,H\,T_s(m,N),                               \tag{6.4}
\]

where `T_s(m,N)>0`. Substitution in (6.3), with both constants retained,
yields

\[
 R_{\rm res}(m,N)
 \le \pi^2\frac{N^2}{H}+\pi^2\sqrt{A_s}\,T_s(m,N).       \tag{6.5}
\]

Because `m>=1`, `H=10^m>1`; because `0<s<1`, `H^{-1}<=H^{-s}`. Hence

\[
 \frac{N^2}{H}\le N^2H^{-s}\le T_s(m,N).                 \tag{6.6}
\]

Combining (6.5)-(6.6), and using
`H^{-s}=(10^m)^{-s}=10^{-sm}`, gives

\[
 \boxed{
 R_{\rm res}(m,N)
 \le C_s\bigl(N+N^2 10^{-sm}\bigr),\qquad
 C_s=\pi^2\bigl(1+\sqrt{A_s}\bigr).}                     \tag{6.7}
\]

Here `C_s>=1`, and it depends on `s` only through `A_s`; it is independent of
`m,N`.

Finally assume, as a separate explicit premise for the same `(mu,c,Q0)`,

\[
 \operatorname{EffectiveIrrationality}(\pi,\mu,c,Q_0).     \tag{6.8}
\]

For each `s`, (6.2)-(6.7) supply exactly the residual estimate and quantifier
order in T2's `PiUniformLongLagResidualPairDecay`. The machine-checked T2
comparator at lines 142-166 then transfers (6.7) to the canonical ordered
collision count with the same `C_s`. Thus (6.2) plus (6.8) is a conditional
route through T8's Fejer argument to C1's exact right-hand side.

Neither (6.2) nor (6.8) is asserted here for `pi`. The almost-everywhere
failure in Section 5 does not obstruct (6.2) merely at fixed `m=1`: there its
right side has order `T_s(1,N)^2`, much larger than the rejected `N^2`
normalization. This observation is only a consistency check, not an
almost-everywhere proof of (6.2) at all scales.

## 7. Conclusions

1. **Almost-everywhere sibling:** at `(mu,c,m)=(8,1,1)`, the exact T8 domain
   represents all ordered unequal pairs, and the identity (4.5) holds with
   exponents `a=0,...,N-1`.
2. **Almost-everywhere sibling:** Philipp's pinned LIL, after checking all ten
   frequency sequences and their quantifiers, gives the failure statement
   (5.9) for Lebesgue-almost every real `alpha` and every `Q0`.
3. **Conditional reduction:** the scale-dependent premise (6.2), together
   with (6.8), yields C1's exact right-hand side with the explicit constant
   `C_s=pi^2(1+sqrt(A_s))`.
4. C1 remains open. No fixed-`pi` spectral claim and no optimality claim for
   (6.2) is made.

## 8. Self-contained replay

From a directory containing only the delivered artifacts, run

```sh
sh verify_sources.sh
```

To inspect the image-only literature locators, render the first two PDF pages:

```sh
pdftoppm -f 1 -l 2 -png -r 180 philipp-1975-lacunary.pdf philipp
```

Inspect `philipp-1.png` right half for journal page 241 and (1.2), then
`philipp-2.png` left half for journal page 242 and (1.8). The derivation is in
Sections 3-6; no finite computation is offered as proof.
