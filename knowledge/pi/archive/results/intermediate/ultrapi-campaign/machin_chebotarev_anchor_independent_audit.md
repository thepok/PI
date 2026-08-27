# Independent audit: Chebotarev obstruction to Machin exact anchors

Audit date: **2026-08-12 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local question has no external source URL; none is invented.

Audited artifacts:

- [`machin_chebotarev_anchor_obstruction.md`](machin_chebotarev_anchor_obstruction.md),
  SHA-256
  `60df072c9afee34d04fb04f9f5435e72e10de494869378d34436e687814de5bc`;
- [`machin_chebotarev_anchor_obstruction_check.py`](machin_chebotarev_anchor_obstruction_check.py),
  SHA-256
  `f5e87ec96df7ffbafef81e99aa1b06b27049184ad4d05621f56cf64a185745ea`.

Independent replay:
[`machin_chebotarev_anchor_independent_check.py`](machin_chebotarev_anchor_independent_check.py),
SHA-256
`e6c46695ec04927b185d85f08202a5c5d4ac15d374faa93e950b472cc52c9ecf`.

## Verdict and exact corrections

**PASS after four narrow precision corrections.**  The field-containment
witness, Chebotarev density subtraction, dyadic-interval consequence,
finite-field incompatibility, T48 instantiation, and final quantifier order
are correct.  The conclusion

\[
 \exists J\ \forall j\ge J\ \forall m\ge0:\quad
 (10^m-16)\operatorname{machinLowerRat}(3j)\notin\mathbb Z
\]

follows unconditionally from the standard Chebotarev theorem and the stated
T48 theorem.

Four edits are required before treating the prose as exact.

1. Section 2 should not call (E=\mathbb Q(\zeta_{16},2^{1/4})) the
   splitting field of (X^4-2) **over (\mathbb Q)**.  Its splitting field
   over (\mathbb Q) is the smaller field
   (\mathbb Q(i,2^{1/4})).  An exact replacement is:

   > Put (F=\mathbb Q(\zeta_{16})).  Over (F), (K/F) and (E/F) are
   > the splitting fields of (X^{16}-10) and (X^4-2), respectively.
   > Over (\mathbb Q), (K) is the splitting field of (X^{16}-10),
   > while (E) is the splitting field of
   > (\Phi_{16}(X)(X^4-2)).  In particular (K,E,L) are finite Galois
   > extensions of (\mathbb Q).

2. The sentence justifying unramifiedness should include the cyclotomic
   factor rather than refer vaguely to “neither polynomial discriminant.”
   An exact replacement is:

   > The only rational primes that can ramify in these splitting fields are
   > among (2) and (5); in particular (5521\nmid 10) is unramified in
   > (K), (E), and (L).

3. Define (\mathcal P) as the rational primes **unramified in (L)** that
   split completely in (K) but not in (L).  This removes the otherwise
   ambiguous scope of “unramified.”  It changes no density or implication.

4. In the finite replay, replace “All regular terms vanish after
   multiplication by (p_0)” with “All regular terms have residue zero
   modulo (p_0) after multiplication by (p_0).”  The rational terms do
   not literally vanish.  Also write the T48 exceptions separately as
   (p\ne239, p\ne317).

These are field-description and residue-language defects, not defects in the
obstruction.  No correction to equations (8)--(25), the asymptotic
quantifiers, or the claimed scope is needed.

The assembled infinite argument has status `proof sketch`; the T48 input is
`machine-checked`; the dated source check below is `literature-checked`; and
both finite scripts are `experiment`.  No fixed return or occurrence theorem
is proved.  Canonical V1 remains a `conjecture`, not a `candidate resolution`.

## 1. Independent field reconstruction

Put (F=\mathbb Q(\zeta_{16})), so ([F:\mathbb Q]=8).

### The field (K)

Let (\alpha^{16}=10).  A prime ideal of (F) above (5) has ramification
index one because (5\nmid16).  Hence its valuation on (10) is exactly
one, and (X^{16}-10) is Eisenstein there.  Thus

\[
 [K:F]=16,\qquad [K:\mathbb Q]=128.
\]

Because (F) contains all sixteenth roots of unity, (K/F) is the splitting
field of (X^{16}-10).  Equivalently, (K/\mathbb Q) is already its full
splitting field and is Galois.

### The field (E)

The identity

\[
 \sqrt2=\zeta_8+\zeta_8^{-1}\in F
\]

shows that (2^{1/4}) has degree at most two over (F).  It is not in (F):
otherwise the nonnormal real field (\mathbb Q(2^{1/4})) would be an
intermediate field of the abelian Galois extension (F/\mathbb Q), whereas
every intermediate field of an abelian Galois extension is Galois.  Therefore

\[
 [E:F]=2,\qquad [E:\mathbb Q]=16.
\]

The field (E) contains (\mu_4), so it contains all roots of (X^4-2).
Together with (F), this proves the corrected Galois description above.

### One splitting prime is enough

For (p_0=5521), exact trial division and modular exponentiation give

\[
 p_0-1=16\cdot345,\qquad
 10^{345}\equiv1,\qquad 2^{1380}\equiv-1\pmod {p_0}.
\]

In a cyclic group of order (5520), the first power test is equivalent to
(10\in(\mathbb F_{p_0}^{\times})^{16}), while the second disproves
(2\in(\mathbb F_{p_0}^{\times})^4).  The independent checker also
enumerates exactly sixteen roots of (x^{16}=10) and no root of (x^4=2).
Since (p_0\equiv1\pmod {16}), it splits in (F), and hence it splits
completely in (K) but not in (E).

If (E\subseteq K), every unramified rational prime split completely in
(K) would split completely in (E) by contraction.  The witness therefore
proves (E\nsubseteq K), hence (K\subsetneq L=KE).  In fact, because
([E:F]=2), it also gives (K\cap E=F), so

\[
 [L:\mathbb Q]=256,qquad [L:K]=2.
\]

Thus the report does not rely on guessing the Kummer intersection; one
certified Frobenius behavior really does prove the strict containment.

## 2. Chebotarev set and the dyadic interval

For a finite Galois extension (H/\mathbb Q), Chebotarev applied to the
identity conjugacy class gives

\[
 \pi_{\mathrm{split},H}(x)
   ={1\over[H:\mathbb Q]}\operatorname{Li}(x)
      +o(\operatorname{Li}(x)).
\]

Every prime split completely in (L) is split completely in (K).  After
excluding the finite ramified set, subtraction therefore gives

\[
 \#\{p\le x:p\in\mathcal P\}
 =\left({1\over128}-{1\over256}\right)\operatorname{Li}(x)
   +o(\operatorname{Li}(x))
 ={1\over256}\operatorname{Li}(x)+o(\operatorname{Li}(x)).
\]

Subtracting the same formula at (x/2) is legitimate: both errors are
(o(x/\log x)), while

\[
 \operatorname{Li}(x)-\operatorname{Li}(x/2)
   \sim{x\over2\log x}.
\]

The resulting count in ((x/2,x]) is asymptotic to
(x/(512\log x)), hence is positive for every sufficiently large (x).
No effective Chebotarev bound, GRH, or Artin primitive-root conjecture is
being smuggled into this step.

The official Thorner--Zaman PDF cited by the primary report was independently
downloaded from Mathematical Sciences Publishers.  Its introduction states
the unconditional Chebotarev asymptotic used here, and its SHA-256 agrees
with the recorded value
`2998c066c04706018052a98fd6cbf9986c14246541c21dbf7db07bb07209c863`:
Jesse Thorner and Asif Zaman,
[*A unified and improved Chebotarev density theorem*](https://doi.org/10.2140/ant.2019.13.1039),
*Algebra & Number Theory* **13** (2019), 1039--1068.

## 3. Permanent incompatibility with (10^m-16)

Let (p\in\mathcal P).  Splitting in (K) gives

\[
 p\equiv1\pmod {16},\qquad
 10\in(\mathbb F_p^\times)^{16}.
\]

If (2) were a fourth power, then (X^4-2) would split over
(\mathbb F_p), since (p\equiv1\pmod {16}) supplies all fourth roots of
unity.  The prime would then split in both (K) and (E), hence in their
compositum (L), a contradiction.  So (2) is not a fourth power.

Writing (2=g^a) in the cyclic group (\mathbb F_p^\times), whose order is
divisible by sixteen, gives the exact equivalence

\[
 16=2^4\in(\mathbb F_p^\times)^{16}
 \quad\Longleftrightarrow\quad16\mid4a
 \quad\Longleftrightarrow\quad4\mid a
 \quad\Longleftrightarrow\quad
 2\in(\mathbb F_p^\times)^4.
\]

Thus (16) is not a sixteenth power.  Every (10^m), including (m=0),
is a sixteenth power, so (10^m\not\equiv16\pmod p) for all (m\ge0).
This verifies the subgroup implication and all of its quantifiers.

## 4. Exact T48 interface, indexing, and scaling

The actual theorem is
`padicValNat_sampledMachinValueRat_den_upperHalfPrime`.  For natural
(N,p), its hypotheses are exactly

\[
 p\text{ prime},\quad5<p,\quad p\ne239,\quad p\ne317,\quad
 12N+15<2p,\quad p\le12N+15,
\]

and its conclusion is exactly

\[
 v_p\!\left(\operatorname{den}
   (\operatorname{sampledMachinValueRat}(N+1))\right)=1.
\]

The imported definition in T46 is

\[
 \operatorname{sampledMachinValueRat}(j)
   =10^j\operatorname{machinLowerRat}(3j).
\]

Consequently the report's (j=N+1), (M_j), and (R_j) substitutions have
no off-by-one or missing-power-of-ten error.  The companion T48 theorem gives
the rational valuation (-1) directly.  Since (p>5), multiplication by
(10^j) is a (p)-adic unit, so the same odd prime also occurs once in the
reduced denominator of (M_j).

Set (x=12N+15).  Chebotarev supplies a (p_N\in(x/2,x]) for every large
enough (N), and (p_N>317) eventually.  T48 then gives

\[
 v_{p_N}(R_{N+1})=-1,
 \qquad v_{p_N}(10^m-16)=0\quad(\forall m\ge0).
\]

Their product has valuation (-1), hence is nonintegral.  If
((10^m-16)M_{N+1}) were integral, multiplying it by the integer
(10^{N+1}) would contradict that fact.  This proves exactly

\[
 \exists J\ \forall j\ge J\ \forall m\ge0,
\]

not merely an unbounded subsequence of (j)'s and not merely a bounded set
of exponents (m).

The current T48 source SHA-256 is
`cbe303cf13da7c60e2c4d602ba97b009a59c3cf49659b2e37d41165a02ab8f3a`.
It is imported by `TheoryLib.lean` and its declarations are registered in
`audit/AxiomAudit.lean`.  A fresh targeted Lean check printed only
`propext`, `Classical.choice`, and `Quot.sound` for the displayed T48
survival theorems.

## 5. Independent full-rational witness

At (N=459), one has

\[
 j=460,\qquad 3j=1380,\qquad12N+15=5523,
 \qquad5523<2\cdot5521.
\]

The literal T36 definitions give 2,762 base-5 terms, with last odd linear
denominator 5,523, and 2,763 base-239 terms, with last denominator 5,525.
Because (2\cdot5521=11042>5525), the sole (5521)-singular linear
denominator is at Taylor index 2,760, whose sign is positive.  Fermat
reduction of the base powers yields

\[
 5521R_{460}\equiv
 10^{460}\left({16\over5}-{4\over239}\right)
 \equiv551\pmod {5521}.
\]

Unlike the primary localized replay, the independent checker constructs the
entire rational

\[
 10^{460}\operatorname{machinLowerRat}(1380)
\]

with `Fraction`, reduces it, and obtains numerator valuation zero,
denominator valuation one, and residue (551) after multiplication by the
prime.  This independently confirms the localization and cancellation
claim rather than assuming it.

The primary checker and targeted Lean file both pass.  The independent
checker prints:

```text
PASS: independent splitting certificate, exact T48 interface, and full-Fraction Machin witness; p=5521, ord_p(10)=345, pR residue=551, bad primes below 100000=41
BOUNDARY: finite computation does not prove Chebotarev density, a fixed return, or V1
```

## Bottom line

The odd-prime obstruction is valid: a positive-density class of primes is
permanently absent from every (10^m-16), while T48 forces one such prime
into every sufficiently deep natural sampled Machin denominator.  The
result rules out exact denominator synchronization for that rational family.
It supplies no Archimedean lower bound on a nonzero residue and therefore no
fixed return, decimal-cylinder hit, or proof of V1.
