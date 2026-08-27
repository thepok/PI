# Maynard aliases under exact mixed-modulus regrouping

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL; none
is invented here.  
Route: the exact shifted-grid reconstruction in
[`actual_shift_resonance_attack.md`](actual_shift_resonance_attack.md), T52's
complete three-primary factor, and the applicability boundary for Maynard's
Lemma 8.2 recorded in
[`three_primary_resonance_literature.md`](three_primary_resonance_literature.md).

## Outcome and claim status

No proof that every finite decimal word occurs in \(\pi\) was obtained. The
canonical V1 target remains a `conjecture`.

There is nevertheless a sharp exact result about the proposed regrouping.
The three-primary denominator **can** be made visible in every digital
frequency by lifting the finite signed reconstruction from modulus
\(M=10^n\) to the coprime product \(MD\), then writing

\[
                    h=aM+bD,
 \qquad {h\over MD}={a\over D}+{b\over M}.          \tag{1}
\]

For \(a\ne0\), the reduced denominator in (1) has a nontrivial factor
coprime to 10. This is a genuine positive answer to the narrow algebraic
question: the \(3\)-part need not disappear from **every** coordinate system.

It does not unlock Maynard's decay. For each fixed \(a\), the complete sum
over \(b\bmod M\) is exactly the original occupancy count, with both the
avoidance vector and the Beatty selector multiplied by the same phase. Thus
the new rows are gauge copies, not new averages. More decisively, Bezout
reciprocity puts the frequency

\[
                         {1\over MD}               \tag{2}
\]

inside a row with a nonzero three-primary component. Its reduced denominator
has \(q_1=D>1\), but its full denominator is \(q=MD\), far outside
Maynard's hypothesis \(q<M^{1/3}\). At this frequency every normalized
digital coefficient supported on \([0,M)\) satisfies

\[
       \left|{|A|}^{-1}\sum_{k\in A}e(k/(MD))\right|
       \ge \cos(\pi/D),                            \tag{3}
\]

so it tends to one as \(D\to\infty\). The missing size hypothesis is
therefore mathematically active, not technical slack.

The elementary identities and separator below have status `proof sketch`
because they have not been formalized in Lean. The exact integer and small
numerical checks are an `experiment`. The Maynard applicability statement is
`literature-checked` as of the audit date through the primary source cited in
Section 7. Nothing here is a V1 resolution.

## 1. Normalized target and quantifier boundary

The canonical statement under investigation is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^m\;
 \exists s\in\mathbb N:\quad
 (d_s(\pi),\ldots,d_{s+m-1}(\pi))=w.              \tag{V1}
\]

Leading zeroes in \(w\) are allowed, \(m=0\) is vacuous, and occurrence is
contiguous. The universal quantifier ranges over **finite** words. The false
uncountable version for arbitrary infinite tails and the distinct subsequence
version are not used. In this branch, \(w\) is fixed but arbitrary; Maynard's
located theorem later narrows further to a one-missing-digit language, and
that narrowing is never silently promoted back to arbitrary \(w\).

## 2. Exact object and finite Beatty selector

Fix a nonempty decimal word \(w\), a depth \(n\), and

\[
 M=10^n,\qquad D=3^A>1,qquad (M,D)=1.              \tag{4}
\]

In the intended T52 range, \(1<D<M\); that inequality is assumed below.
Let \(A_w(n)\subset\{0,\ldots,M-1\}\) be the leading-zero-padded
length-\(n\) strings avoiding \(w\). At one actual shifted grid, write

\[
 \theta={r\over F}\in[0,1),\qquad
 x_c={c+\theta\over D},\qquad 0\le c<D,             \tag{5}
\]

where \(\theta/D=r/(FD)\) is the shift used in the companion report. Put

\[
                         t=\lfloor M\theta\rfloor. \tag{6}
\]

Since \(Mc+t\) is an integer and \(0\le M\theta-t<1\), adding the final
fraction cannot cross a multiple of the integer \(D\). Hence the sampled
length-\(n\) prefix is exactly

\[
       q_c=\lfloor Mx_c\rfloor
          =\left\lfloor{Mc+t\over D}\right\rfloor. \tag{7}
\]

Define the Beatty selector on \(0\le k<M\) by

\[
 W_t(k)=\mathbf 1_{\{q_0,\ldots,q_{D-1}\}}(k).     \tag{8}
\]

The points in (7) are distinct because their unrounded spacing is
\(M/D>1\) in the intended range. An endpoint-safe alternative formula is

\[
 W_t(k)=
 \left\lceil{D(k+1)-t\over M}\right\rceil
 -\left\lceil{Dk-t\over M}\right\rceil.            \tag{9}
\]

It counts the integers \(c\) in the half-open interval

\[
              {Dk-t\over M}\le c<{D(k+1)-t\over M}.
\]

Consequently the exact shifted-grid occupancy is the finite inner product

\[
 N=\sum_{c=0}^{D-1}\mathbf 1_{A_w(n)}(q_c)
  =\sum_{k=0}^{M-1}\mathbf 1_{A_w(n)}(k)W_t(k).     \tag{10}
\]

Formula (10) encodes the full actual shift through \(t\). It is the finite,
boundary-safe counterpart of the signed Poisson reconstruction; no phase or
endpoint information is dropped.

## 3. Why valuation-grouping cannot alter the original denominator

In the Poisson formula, the digital coefficient occurs at

\[
                         {\ell D\over M}.          \tag{11}
\]

Because \((D,M)=1\), its reduced denominator is identically

\[
                   {M\over(\ell,M)},               \tag{12}
\]

which has only the primes 2 and 5. Partitioning \(\ell\) according to
\(v_3(\ell)\), according to its base-10 valuation, or into dyadic/Vaaler
blocks changes neither (11) nor (12).

There is a particularly easy false maneuver to exclude. One may write

\[
 {\ell D\over M}={\ell D^2\over MD}
\]

and point to the factor \(D\) in the displayed denominator. But the numerator
is also divisible by \(D\). Maynard's lemma requires the rational numerator
to be coprime to its denominator; reducing the fraction cancels \(D\) and
returns (12). Thus no direct regrouping of the original \(\ell\)-sum can
manufacture \(q_1>1\).

A Vaaler or Fejer approximation has the same invariant. Such an
approximation merely truncates or reweights integer circle modes \(h\).
Averaging it over a \(D\)-grid forces \(D\mid h\), so the digital arguments
remain \(\ell D/M\), with reduced denominator (12).

## 4. The exact CRT lift where the three-primary factor really survives

For functions \(A(k)=\mathbf 1_{A_w(n)}(k)\) and \(W(k)=W_t(k)\) on
\(0\le k<M\), define, for \(a\bmod D\) and \(b\bmod M\),

\[
 \begin{aligned}
 \mathcal A_a(b)&=\sum_{k=0}^{M-1}A(k)
       e\!\left(-k\left({a\over D}+{b\over M}\right)\right),\\
 \mathcal W_a(b)&=\sum_{k=0}^{M-1}W(k)
       e\!\left(-k\left({a\over D}+{b\over M}\right)\right).
 \end{aligned}                                      \tag{13}
\]

The map

\[
 (a,b)\longmapsto h=aM+bD\pmod {MD}                 \tag{14}
\]

is a bijection because \((M,D)=1\). Thus (13) is exactly the length-\(MD\)
Fourier grid, written in CRT coordinates; it is not an approximation.

The reduced denominator of (1) factors exactly. Since

\[
 \begin{aligned}
 (aM+bD,D)&=(a,D),\\
 (aM+bD,M)&=(b,M),
 \end{aligned}
\]

and \((M,D)=1\), it is

\[
 q(a,b)=
 \underbrace{{D\over(a,D)}}_{q_1(a)}
 \underbrace{{M\over(b,M)}}_{q_2(b)}.              \tag{15}
\]

For every \(1\le a<D\), \(q_1(a)>1\) and
\((q_1(a),10)=1\). This is the promised legitimate appearance of a
non-base denominator: unlike the fake fraction after (12), it survives
reduction.

## 5. Gauge-row identity: the new denominator gives no new average

For every fixed \(a\bmod D\), finite Fourier orthogonality in the
\(b\)-coordinate gives

\[
 \boxed{
 {1\over M}\sum_{b=0}^{M-1}
       \mathcal A_a(b)\overline{\mathcal W_a(b)}=N.}           \tag{16}
\]

Indeed, expanding the left side produces

\[
 \sum_{k,l}A(k)W(l)e(a(l-k)/D)
 \left({1\over M}\sum_{b=0}^{M-1}e(b(l-k)/M)\right).
\]

Because \(0\le k,l<M\), the parenthesized term is one exactly when
\(k=l\), and zero otherwise. On the diagonal the modulation
\(e(a(l-k)/D)\) is one, leaving (10).

Equivalently, the full length-\(MD\) Parseval identity is

\[
 N={1\over MD}\sum_{a=0}^{D-1}\sum_{b=0}^{M-1}
       \mathcal A_a(b)\overline{\mathcal W_a(b)},              \tag{17}
\]

but each of its \(D\) rows contributes exactly \(N/D\). The \(a=0\) row is
the ordinary length-\(M\) signed reconstruction. Every \(a\ne0\) row is the
same reconstruction after multiplying both vectors by the same character
\(e(-ak/D)\).

This is the main separator. CRT does expose a non-base factor, but it does
so by a gauge modulation that cancels from the inner product. A bound must
still control a complete \(b\)-row. There is no new averaging over actual
Machin phases and no loss of the Beatty selector.

### Pure triadic coefficients are insufficient

The column \(b=0\) contains the attractive coefficients

\[
              \mathcal A_a(0)=\sum_kA(k)e(-ak/D),              \tag{18}
\]

to which a Maynard-type rational-frequency estimate can apply. But this
column does not determine \(N\). An exact linear-algebra separator is enough.
Assume \(M>D(D+1)\), take \(t=0\), and compare the singleton vectors

\[
                         A_0=\{0\},\qquad A_1=\{D\}.            \tag{19}
\]

They have identical residue histograms modulo \(D\), hence identical values
of (18) for every \(a\). Yet \(0=q_0\) is sampled, while every positive
sample is at least \(\lfloor M/D\rfloor>D\); therefore

\[
                    \langle A_0,W_0\rangle=1,
             \qquad \langle A_1,W_0\rangle=0.                 \tag{20}
\]

This does not model a forbidden-word language and is not a counterexample to
an estimate using that language's full structure. It proves only the exact
claim needed here: denominator-\(D\) Fourier data alone cannot reconstruct
the sparse Beatty occupancy.

## 6. Bezout reciprocity creates an ultra-major non-base alias

Let

\[
              a_*\equiv M^{-1}\pmod D,qquad1\le a_*<D,
 \qquad       b_*={1-a_*M\over D}\in\mathbb Z.                \tag{21}
\]

Then Bezout's identity gives exactly

\[
 \boxed{{a_*\over D}+{b_*\over M}={1\over MD}.}               \tag{22}
\]

Replacing \(b_*\) by its residue modulo \(M\) only adds an integer to the
frequency, so (22) occurs in the valid nonzero row \(a=a_*\) of (16).
By (15), its reduced denominator has

\[
                         q_1=D,qquad q_2=M,qquad q=MD.        \tag{23}
\]

Thus reciprocity does not turn a base major alias into a useful
denominator-\(D\) minor arc. It hides the major alias on a diagonal where
the two rational summands in (22) almost cancel.

This failure is quantitatively sharp. Let \(A\) be any nonempty subset of
\(\{0,\ldots,M-1\}\). The points \(e(k/(MD))\), \(k\in A\), all lie on an
arc of angular width strictly less than \(2\pi/D\). Rotating that arc to be
centered on the positive real axis shows that every term has real part at
least \(\cos(\pi/D)\). Hence

\[
 \boxed{
 \left|{1\over|A|}\sum_{k\in A}e(k/(MD))\right|
       \ge\cos(\pi/D).}                                         \tag{24}
\]

The same bound holds for the normalized Beatty transform
\(D^{-1}\mathcal W_{a_*}(b_*)\). In the intended T52 schedule
\(D\asymp n\), both lower bounds tend to one.

The obstruction is also visible inside Maynard's proof. At the frequency
\(u=1/(MD)\), for every digit place \(0\le i<n\),

\[
 \|10^iu\|={10^i\over D10^n}\le{1\over10D},
 \qquad
 \sum_{i=0}^{n-1}\|10^iu\|^2<{1\over99D^2}.                   \tag{25}
\]

Maynard obtains decay by proving that this sum of squared distances grows
linearly in the number of suitable digit blocks. Equation (25) is the
opposite extreme. All \(n\) digit factors stay on the same major arc; a
block factorization merely postpones the visible rational \(1/D\) until
after the final available digit.

## 7. What Maynard's Lemma 8.2 genuinely controls here

Primary source: J. Maynard,
[*Primes with restricted digits*](https://arxiv.org/abs/1604.01041),
Inventiones Mathematicae 217 (2019), 127--218,
[DOI 10.1007/s00222-019-00865-6](https://doi.org/10.1007/s00222-019-00865-6).
The exact locator is Lemma 8.2, restated and proved as Lemma 10.1.

For the normalized one-missing-digit Fourier product \(F_M\), the lemma
states that if

\[
 q<M^{1/3},\qquad q=q_1q_2,qquad(q_1,10)=1,qquad q_1>1,
 \qquad |\eta|<M^{-2/3}/2,                         \tag{26}
\]

then at a reduced numerator it gives

\[
 F_M(A/q+\eta)\ll
 \exp\!\left(-c{\log M\over\log q}\right).        \tag{27}
\]

There is a valid narrow substitution in (13). Reduce

\[
 {a\over D}={a_0\over q_1},qquad q_1={D\over(a,D)}>1.
\]

For a centered representative \(b\) satisfying

\[
                         |b|<M^{1/3}/2,            \tag{28}
\]

take \(q=q_1\), \(q_2=1\), and \(\eta=b/M\). Since
\(D\asymp n\ll M^{1/3}\) in the intended application, all hypotheses in
(26) hold eventually, and (27) gives genuine decay for these mixed modes.
Likewise, (15) permits some exact-rational substitutions with \(\eta=0\)
when the **full** reduced denominator \(q_1q_2<M^{1/3}\).

Neither statement covers (22), where \(q=MD\), and neither bounds the full
row in (16). The strong estimate therefore controls a real minor-arc region
of the CRT lift, but the complementary diagonal base-major region survives.
The identity (24) proves that no extension depending only on \(q_1>1\) can
cover that region.

Maynard's result is also specific to one missing digit. Extending its product
estimate to an arbitrary forbidden word would require a transfer-matrix
analogue, and even such an extension would still face (22)--(25).

## 8. Audit of the proposed escape routes

### Grouping by \(3\)-adic or base valuation

This remains in the original frequency coordinate (11). Equation (12)
proves that every reduced denominator is a power of 2 times a power of 5.
The \(3\)-adic label of \(\ell\) is not a \(3\)-part of that denominator.

### Poisson reciprocity

The exact CRT/Bezout reciprocity is (22). It really introduces \(D\), but
also introduces the compensating base fraction \(b_*/M\), leaving the
ultra-small frequency \(1/(MD)\). Equations (23)--(25) put it outside the
Maynard range and inside the strongest digital major arc.

### Vaaler or Fejer kernels

Applied before grid averaging, they preserve (11)--(12). Applied after the
Beatty reduction, they amount to approximating \(W_t\); an exact result must
recover the inner product (10), and the exact mixed reconstruction is still
(16). A truncation error cannot be declared small merely from the measure of
the avoidance set: under the missing-word hypothesis, the actual sampled
point is precisely a survivor.

### Summing the non-base rows

Equation (17) may suggest cancellation in \(a\). Equation (16) forbids this:
after the complete \(b\)-sum, every row equals the same real integer \(N\).
Any cancellation seen before completing a row must be paid back by its
uncontrolled modes.

### Using only rational frequencies \(a/D\)

Those are the \(b=0\) column. Equations (19)--(20) prove that this column,
even in its entirety, does not determine Beatty occupancy. Extra quotient or
within-cell information is indispensable, and adding it recreates the
mixed/base modes of (13).

## 9. Reproducible checker (`experiment`)

[`maynard_alias_regrouping_check.py`](maynard_alias_regrouping_check.py)
uses integer arithmetic for the Beatty identities, denominator
factorizations, CRT aliases, gauge orthogonality, and the pure-triadic
separator. It uses small complex DFTs and digit products only as numerical
reproducibility checks. It does not read digits of \(\pi\).

Commands:

```bash
python3 -m py_compile \
  work/ultrapi-resume/maynard_alias_regrouping_check.py
python3 work/ultrapi-resume/maynard_alias_regrouping_check.py
```

Retained output:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
beatty_indicator_exact_checks=444400
original_base_denominator_exact_checks=444404
mixed_denominator_factorization_exact_checks=8379300
gauge_row_orthogonality_exact_checks=120
gauge_row_numeric_dft_checks=3
gauge_row_max_numeric_error=1.433e-14
pure_triadic_data_separator_exact_checks=4
diagonal_major_alias_exact_checks=4
diagonal_major_alias_rows=[(2, 3, 0.8085214934039193, 0.8425196397504662, 0.5000000000000001), (3, 9, 0.9776494412657084, 0.9800592813362985, 0.9396926207859084), (4, 27, 0.9975030066685355, 0.9977481725691679, 0.993238357741943), (5, 81, 0.9997223879684317, 0.9997493432134263, 0.99924795250423), (6, 243, 0.999969152139962, 0.9999721436023794, 0.9999164298554373)]
all exact assertions and numerical reproducibility checks passed
```

The five tuple fields are \((n,D,|F_M(1/(MD))|,\) normalized Beatty-transform
magnitude, \(\cos(\pi/D))\). Their convergence toward one illustrates (24);
the general bound comes from the arc argument, not from these finite rows.

## 10. Sharp conclusion

The regrouping question now has a clean answer.

1. In the original Poisson/Vaaler coordinate, a three-primary denominator
   cannot enter: reduction gives (12).
2. In the exact CRT coordinate, it does enter through (15).
3. The complete non-base rows are gauge copies of the same occupancy count by
   (16), not independent averages.
4. Every such lift contains diagonal major aliases; (22)--(25) exhibit one
   whose normalized digital coefficient tends to one while \(q_1=D>1\).
5. Maynard's lemma gives legitimate decay on a minor-arc portion of the lift,
   but its full-modulus bound excludes exactly these aliases.

This is a `proof sketch` separator against obtaining ASR merely by
relabeling the full signed reconstruction and invoking Maynard's Lemma 8.2.
It does not rule out a new theorem that combines the exact actual Machin
phase, the Beatty transform \(\mathcal W_a(b)\), and cancellation across the
remaining mixed modes. That arithmetic input remains the unresolved part of
ASR.
