# T96: A fixed non-pi seed with exponentially slow times-16 transversals

Status: **machine-checked** in `T96FixedSeedSibling.lean`, with an independent
numbered derivation and exact finite replay below. This is an explicitly non-pi
sibling theorem, not a result about the canonical fixed-pi question.

## Provenance and dependency discipline

The immutable canonical statement is vendored as
`pi-positive-decimal-factor-entropy.txt`, SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
It was formulated locally and has no external source URL.

The Lean companion imports only the kernel-checked research module
`TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore`.
In particular, this note uses T44's `DecimalStream`, `circleValue`,
`AvoidsWord`, `KWord`, and `Core`, and its checked shift, closedness, and
forward-invariance theorems.  T57 and T78 are comparisons only: T57 has a
moving word on a fixed rational compact set, while T78 has both a moving word
and a scale-dependent irrational seed.  No claim from T57 or T78 is a premise
below. Neither comparison module is imported by the Lean file.

## Normalized sibling statement

Put

\[
  x_*:=\sum_{q=1}^{\infty}10^{-4^q},\qquad
  \xi_*:=(x_*:\mathbb R/\mathbb Z),\qquad R_m:=2^m,
\]

and define the fixed-seed decimal orbit closure

\[
  K_{x_*}:=\overline{\{10^n\xi_*:n\in\mathbb N\}}
  \quad\text{in }\mathbb R/\mathbb Z.
\]

**Sibling theorem.** For every integer \(m\ge5\), there is a word
\(w_m\in\{0,\ldots,9\}^m\) of exact length \(m\) such that

\[
  K_{x_*}\subseteq \operatorname{Core}(w_m,R_m).
\]

Here T44's inclusive convention is used: membership in `Core(w,R)` requires
avoidance after every decimal shift and at every level \(0\le j\le R\).
`KWord` is existential in the decimal expansion, so terminating endpoints and
their repeating-nine alternatives are handled safely.

The quantifiers are

\[
  \forall m\ge5\;\exists w_m\;\forall y\in K_{x_*}\;\forall n\ge0\;
  \forall 0\le j\le2^m,
\]

with an avoiding expansion allowed to depend on \(m,y,n,j\).  The seed
\(x_*\) is fixed before \(m\), but the omitted word is allowed to vary with
\(m\).

## Numbered proof

The Lean proof uses the safe fixed width `blockWidth j = 2*j+1` (allowing
leading zeros) rather than the exact width `ell_j` used in this readable
derivation. It defines the least power-of-four split with `Nat.find`, proves
`splitEnd <= 2*(blockWidth j+m)`, and obtains the same global bound. The
acceptance-facing theorem
`DecimalFactorEntropy.T96FixedSeedSiblingExplicit.fixed_seed_sibling_certificate`
ties together the literal one-based series, irrationality, non-pi scope,
factor bound, all-window coverage, scaled values, avoidance, exact word length,
radius, and Core containment without additional hypotheses.

### 1. Elementary size and irrationality

The series is positive.  Since \(4^q\ge q+3\) for \(q\ge1\),

\[
  0<x_*\le\sum_{q=1}^{\infty}10^{-(q+3)}=\frac1{9000}<1. \tag{1.1}
\]

For \(Q\ge1\), write \(E=4^Q\),

\[
  S_Q=\sum_{q=1}^{Q}10^{-4^q},\qquad T_Q=x_*-S_Q.
\]

For every \(k\ge0\), \(4^{Q+1+k}\ge4^{Q+1}+k=4E+k\).  Therefore

\[
  0<T_Q\le\sum_{k=0}^{\infty}10^{-(4E+k)}
    =\frac{10}{9}10^{-4E}<2\,10^{-4E}. \tag{1.2}
\]

Suppose that \(x_*=a/b\), where \(a\in\mathbb Z\), \(b\ge1\).  Choose
\(Q\) so large that \(2b<10^{3E}\).  The number \(10^E S_Q\) is an
integer.  Hence

\[
  b10^E T_Q=b10^Ex_*-b10^ES_Q
\]

is an integer.  But (1.2) gives

\[
  0<b10^ET_Q<2b10^{-3E}<1,
\]

a contradiction.  Thus \(x_*\) is irrational.  In particular the fixed seed
is not a disguised terminating endpoint.

Also, \(x_*\ne\pi\): (1.1) gives \(x_*<1\), whereas the standard
kernel-checked inequality `Real.pi_gt_three` gives \(3<\pi\).

### 2. Parameters for one times-16 level

Fix \(m\ge5\), put \(R=2^m\), and fix \(0\le j\le R\).  Let

\[
  N_j=16^j
\]

and let \(\ell_j\) be the exact number of decimal digits of \(N_j\).  Since
\(16^j<10^{2j+1}\),

\[
  1\le\ell_j\le2j+1. \tag{2.1}
\]

Let \(Q_j\ge1\) be the least integer such that

\[
  \ell_j+m\le3\cdot4^{Q_j}, \tag{2.2}
\]

and put \(E_j=4^{Q_j}\).  If \(Q_j=1\), then \(E_j=4\le\ell_j+m\).
If \(Q_j>1\), minimality gives

\[
  \ell_j+m>3\cdot4^{Q_j-1}=\frac34E_j.
\]

In both cases,

\[
  E_j\le2(\ell_j+m). \tag{2.3}
\]

### 3. The finite prefix

The first \(Q_j\) summands of \(N_jx_*\) have common denominator
\(10^{E_j}\):

\[
  N_j\sum_{q=1}^{Q_j}10^{-4^q}
   =\frac{A_j}{10^{E_j}},\qquad
  A_j=N_j\sum_{q=1}^{Q_j}10^{E_j-4^q}\in\mathbb Z. \tag{3.1}
\]

Let \(p_j\) be the residue of \(A_j\) modulo \(10^{E_j}\), with
\(0\le p_j<10^{E_j}\).  Thus the fractional part of (3.1) is
\(p_j/10^{E_j}\), represented by an exact block of \(E_j\) digits, allowing
leading zeros and followed by terminating zeros.

### 4. Carry-free disjoint tail

The remaining summand with index \(q>Q_j\) places the \(\ell_j\)-digit word
for \(N_j\) in the one-based decimal interval

\[
  I_{j,q}=[4^q-\ell_j+1,\,4^q]. \tag{4.1}
\]

There are exactly

\[
  (4E_j-\ell_j+1)-E_j-1=3E_j-\ell_j\ge m \tag{4.2}
\]

zero positions between the finite prefix and the first tail block.  Between
successive tail blocks there are exactly

\[
  (4^{q+1}-\ell_j+1)-4^q-1
   =3\cdot4^q-\ell_j\ge m. \tag{4.3}
\]

Thus the intervals are pairwise disjoint, and no length-\(m\) window can meet
two pieces.

It remains to exclude a carry from the whole tail into the prefix.  From the
same geometric estimate as (1.2), and from
\(\ell_j\le3E_j-m\),

\[
\begin{aligned}
  U_j&:=N_j\sum_{q>Q_j}10^{-4^q}\\
     &<2N_j10^{-4E_j}
      <2\,10^{\ell_j-4E_j}
      \le2\,10^{-E_j-m}<10^{-E_j}. \tag{4.4}
\end{aligned}
\]

Since \(p_j/10^{E_j}\le1-10^{-E_j}\), (4.4) implies

\[
  0\le\frac{p_j}{10^{E_j}}+U_j<1. \tag{4.5}
\]

Consequently reduction modulo one causes no cross-scale carry.  Define
\(d^{(j)}\) to be the stream consisting of the exact \(E_j\)-digit block for
\(p_j\), the copies of the decimal digits of \(N_j\) on the intervals
\(I_{j,q}\), and zeros elsewhere.  Disjointness permits termwise summation,
and (3.1), (4.4), and (4.5) give the exact identity

\[
  \operatorname{ofDigits}(d^{(j)})
    =\operatorname{frac}(16^jx_*). \tag{4.6}
\]

This is an equality of an explicit decimal expansion, not an appeal to a
floating-point approximation.

### 5. Factor count for one level

At most \(E_j\) length-\(m\) factors start in the finite prefix.  Any later
nonzero factor meets exactly one copy of the \(\ell_j\)-digit word for
\(N_j\).  Relative to one zero-padded copy, there are
\(\ell_j+m-1\) starting offsets that meet it; adding the all-zero factor gives
at most \(\ell_j+m\) possibilities.  Therefore

\[
  |F_j(m)|\le E_j+\ell_j+m
    \le3(\ell_j+m). \tag{5.1}
\]

The first bound deliberately allows duplicate factors and therefore remains
an upper bound at decimal endpoints.

### 6. Count over every inclusive level

Using (2.1),

\[
  \sum_{j=0}^{R}\ell_j
   \le\sum_{j=0}^{R}(2j+1)=(R+1)^2. \tag{6.1}
\]

Hence the union of all length-\(m\) factors in the \(R+1\) streams has size
at most

\[
\begin{aligned}
  \left|\bigcup_{j=0}^{R}F_j(m)\right|
   &\le3\sum_{j=0}^{R}(\ell_j+m)\\
   &\le3(R+1)(R+m+1)\\
   &\le12R^2\\
   &\le40R^2=40\cdot4^m. \tag{6.2}
\end{aligned}
\]

For the third line, \(m\ge5\) implies \(m+1\le R=2^m\), while
\(R+1\le2R\).

The final strict comparison starts at

\[
  40\cdot4^5=40960<100000=10^5. \tag{6.3}
\]

Increasing \(m\) multiplies the left side by \(4\) and the right side by
\(10\), so induction gives

\[
  40\cdot4^m<10^m\qquad(m\ge5). \tag{6.4}
\]

There are exactly \(10^m\) decimal words of length \(m\).  Equations (6.2)
and (6.4) therefore select a word \(w_m\) absent from every
\(d^{(j)}\), simultaneously for all \(0\le j\le R\).  Its length is exactly
\(m\).  This word is selected separately at each \(m\); no fixed-word claim
is made.

### 7. Shifted avoidance and T44 Core membership

For each \(j\le R\), (4.6) says that `circleValue d^(j)` is
`circleMul (16^j) xi_*`, and the choice in step 6 says that `d^(j)` avoids
`w_m`.  Every `streamShift n d^(j)` also avoids `w_m`.  T44's checked shift
identity and commutation give

\[
\begin{aligned}
 \operatorname{circleValue}(\operatorname{streamShift}_n d^{(j)})
  &=10^n\operatorname{circleValue}(d^{(j)})\\
  &=10^n16^j\xi_*=16^j10^n\xi_*.
\end{aligned} \tag{7.1}
\]

Thus the shifted stream is an endpoint-safe existential witness for every
pair \((n,j)\), exactly the quantifiers in T44's `Core`. The machine-checked
theorems `scaledExpansion_circleValue`,
`scaledExpansion_avoids_omittedWord`, and `xStarPoint_mem_Core` in namespace
`DecimalFactorEntropy.T96FixedSeedSiblingExplicit` discharge these obligations
for the explicit seed and selected word.

### 8. Orbit closure containment

T44 proves that `Core(w_m,R)` is forward-times-10 invariant and closed.  Step
7 first puts \(\xi_*\) in the core; forward invariance puts every
\(10^n\xi_*\) in it; closedness then yields

\[
  K_{x_*}\subseteq\operatorname{Core}(w_m,R_m). \tag{8.1}
\]

This last passage is machine-checked as
`DecimalFactorEntropy.T96FixedSeedSiblingExplicit.xStarOrbitClosure_subset_Core`;
the exact requested quantifiers are exported by `fixed_seed_sibling_theorem`.
No preferred expansion is chosen for a closure point.

## Exact replay

Run, in a directory containing only these delivered files,

```sh
python3 t96_exact_replay.py --verify replay_expected.json
```

or run `sh verify.sh` to check both hashes and replay output.  The checker uses
only exact Python integers and strings.  It verifies the pinned source hash,
the finite base inequality (6.3), the induction multipliers in (6.4), every
integer inequality used in (2.1)--(6.2) for all \(5\le m\le8\), and directly
constructs the structural factor sets from steps 3--5.  For every checked
\((m,j)\), it also independently materializes the exact finite prefix and the
first two tail blocks at positions \(4^q\), checks the cleared-denominator
rational identity, and confirms that its factors equal the structural model.
These finite checks are audit aids, not a proof of the infinite series or the
universal quantifiers; those are discharged by the numbered arguments above.

## Scope

- \(x_*\) is one fixed irrational real and is not \(\pi\).
- The word \(w_m\) varies with \(m\).
- The conclusion is only the stated fixed-seed sibling theorem.
- No conclusion is made about \(K_\pi\), C6, C1, decimal factor entropy of
  \(\pi\), or the canonical question.
- T57 and T78 are comparisons only and are not logical dependencies.
