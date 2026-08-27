# BBP moving diagonal versus density theorems for fractional parts of powers

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is Marcel's local, human-authored question and has no
external source URL; none is invented here.

Frozen branch input:

- [bbp_dyadic_diagonal_functional_recurrence_20260813.md](bbp_dyadic_diagonal_functional_recurrence_20260813.md),
  SHA-256
  `8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba`;
- its checker,
  SHA-256
  `c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651`.

## Outcome and claim boundary

The literature application is negative but sharp.  None of the checked
theorems about

\[
 \{a^n/n\},\qquad \{Q(\alpha^n)/n\},\qquad
 \{a^{f(n)}/n^d\}
\]

applies to the seven BBP forcing phases.  In the cited theorems the
denominator is the same freely chosen index (or its literal power), and the
base is a fixed integer or a Pisot/Salem algebraic integer.  The BBP lift has
the fixed **rational modular base**

\[
                 R=5\,2^{-27},                              \tag{1}
\]

exponent \(n+1\), and an affine or quartic polynomial modulus.  Replacing a
quartic polynomial by its asymptotic size \(Cn^4\) is invalid for modular
residues.

Splitting the BBP coefficient is useful, but it does not produce 28
independent instances of a known theorem.  There are 28 formal linear poles.
At the seventh phase, two are not two-adically integral **as written**.
Nevertheless, their sum has an exact Bézout recombination into two
integer-numerator fractions with the same two odd linear denominators.  The
sharp direct endpoint is therefore

\[
                    \boxed{28\text{ odd-linear terms}.}       \tag{2}
\]

In particular, the tempting \(26\)-linear-plus-one-quadratic endpoint is
valid as an intermediate pairing but is not maximal.  Section 3 gives and
checks the missing identity.

There is one new exact adaptation target.  If an odd-linear modulus
\(L(n)=An+B\) happens to be prime, its selected BBP residue is one
distinguished root of a **fixed binomial congruence** of degree
\(A\in\{14,28,56\}\).  Existing root-distribution theorems average all roots
or all moduli; they do not control this distinguished root, the affine prime
subsequence, or the simultaneous 28-coordinate vector.  For composite
\(L(n)\), even the local binomial depends on the complementary cofactor, so
the standard Chinese-remainder set theorem does not instantiate.

Finally, even a uniformly distributed forcing subsequence together with a
much stronger shrinking-interval covering rate than the 2013 theorem does
**not** imply target hitting for

\[
                  X_{n+1}=\{10X_n+\Gamma_n\}.                \tag{3}
\]

An exact van-der-Corput countermodel below keeps every state in
\([0,1/10)\) while its forcing has both properties.  This is a logical
separator only; it does not model the arithmetic BBP forcing.

The source audit is `literature-checked`.  The exact algebraic reductions and
logical separators have status `proof sketch`; the finite replay is an
`experiment`.  Canonical V1 remains a `conjecture`.  Nothing here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`, and
no occurrence of a prescribed decimal word is proved.

## 1. Target and quantifiers kept fixed

Canonical V1 is

\[
 \forall m\ge0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists r\ge0\ \forall i<m:\quad d_{r+i}(\pi)=w_i.          \tag{4}
\]

Occurrence is contiguous, leading zeroes are allowed, and the empty word is
vacuous.  This audit does not replace V1 by normality, single-digit
recurrence, an infinite suffix, or a noncontiguous subsequence.

The phrase "split into 28 linear moduli" has two different readings which
must not be conflated:

1. partial-fraction the rational BBP coefficient before taking its dyadic
   residue;
2. Chinese-remainder split the already constructed residue
   \(h_{n,j}/d_{n,j}\).

Section 3 treats the first operation and Section 4 treats the second.  They
have different obstructions.

For reference, the frozen unsplit phase has

\[
 \begin{aligned}
 k_{n,j}&=7n+j,\\
 d_{n,j}&=(2k_{n,j}+1)(4k_{n,j}+3)
            (8k_{n,j}+1)(8k_{n,j}+5),\\
 h_{n,j}&\equiv-(120k_{n,j}^2+151k_{n,j}+47)
  2^{4(7-j)}R^{n+1}\pmod {d_{n,j}},                \tag{T}
 \end{aligned}
\]

with \(R\) as in (1), and
\(\Gamma_n=\{\sum_{j=1}^7h_{n,j}/d_{n,j}+b_n/M_n\}\).
These are the concrete parameters against which every theorem below is
tested.

## 2. What the primary theorems actually prove

The following PDFs were retrieved and read on 2026-08-13.  Hashes pin the
bytes inspected, not merely bibliographic landing pages.

| source | inspected PDF SHA-256 | exact useful scope |
|---|---|---|
| Cilleruelo--Kumchev--Luca--Rué--Shparlinski, [*On the Fractional Parts of \(a^n/n\)*](https://upcommons.upc.edu/bitstreams/ae5e82a0-9bb2-4dd3-8dbc-b22da011adf5/download), [DOI](https://doi.org/10.1112/blms/bds084) | `e5ab04087aa7f162b9431a003c16ccba9558d32f5e088ec7565bf6d6c2154164` | For fixed integer \(a\ge2\), Theorem 1 gives \(D(N)=O(\log\log\log\log N/\log\log\log N)\) on the explicit semiprime subsequence \(\mathcal A=\{pq:p,q\text{ prime},\ q\le\log p/\log a\}\).  Theorem 2 says that for every \(c>0\) and all sufficiently large \(N\), the first \(N\) terms hit every interval of length at least \(cN^{-0.475}\).  Numerator exponent and denominator index are both \(n\). |
| Dubickas, [*Density of some sequences modulo 1*](https://www.impan.pl/shop/en/publication/transaction/download/product/87011), [DOI](https://doi.org/10.4064/cm128-2-9) | `9b16c0a16187f9a9e75475e25abbf9c11c7f79b69ebafe340d7762ca60f0bf0e` | Theorem 1.2 treats \(\{Q(\alpha^n)/n\}\) for a Pisot or Salem number \(\alpha\).  The paper explicitly records \(\{Q(\alpha^n)/P(n)\}\) with \(\deg P\ge2\) as a desired extension, not a theorem. |
| Dubickas, [*Density of Some Special Sequences Modulo 1*](https://epublications.vu.lt/object/elaba%3A164926835/164926835.pdf), [DOI](https://doi.org/10.3390/math11071727) | `74bc3bdd4b05d6ebff3935f1dc4cddca37990fc6288a90946a2449ebc21149cd` | Theorem 1 describes the attained values of \(\{a^{f(n)}/n\}\).  Theorem 2 proves density of \(\{a^{f(n)}/n^d\}\) for fixed integers \(a\ge2,d\ge1\), \(f\in\mathbb Z[x]\) nonconstant with positive leading coefficient, and \(\operatorname{rad}(d)\mid\operatorname{rad}(a)\).  Here \(n^d\) is literally a power of the same index. |
| Lind, [*Some remarks related to the density of \(\{(b^n\bmod n)/n\}\)*, arXiv:2308.14354v2](https://arxiv.org/abs/2308.14354v2), [inspected PDF](https://arxiv.org/pdf/2308.14354v2) | `d02adcb8aeb29fb5ac9e6d4be79ebb81728aef939e04e3f8ebd80f3959f5156e` | Theorem 1 identifies the limit points of \(b^{qp}\bmod(qp)\) over primes \(p\), for fixed prime \(q>b^2\), and recovers density.  It again uses exponent and modulus \(qp\) together. |
| Kowalski--Soundararajan, [*Equidistribution from the Chinese Remainder Theorem*, arXiv:2003.12965v2](https://arxiv.org/abs/2003.12965v2), [inspected PDF](https://arxiv.org/pdf/2003.12965v2), [DOI](https://doi.org/10.1016/j.aim.2021.107776) | `82bf98763cd587fd77c07df08ff4583623a9a9b7b9d5b0a0fc2f9e76d425b809` | Equidistributes the uniform measures on **all** members of compatible local sets \(A_{p^v}\), combined by CRT, for typical moduli.  The local set is fixed by \(p^v\), not by the complementary cofactor, and a singleton set has discrepancy one.  Its introduction also records higher-degree roots over prime moduli as an outstanding problem. |

The 2013 short-interval proof is especially rigid.  It takes \(n=pq\),
chooses \(p\equiv1\pmod{q-1}\), and reduces

\[
              \frac{a^{pq}}{pq}\equiv\frac{a^q}{pq}\pmod1. \tag{5}
\]

Prime gaps then move the ordinary ratio \(a^q/(pq)\) through the unit
interval.  If instead an affine modulus is set equal to \(pq\), the BBP
exponent becomes \((pq-B)/A+1\), so (5) disappears.  This is not a cosmetic
change in notation; it removes the congruence on which the interval sweep is
built.

The 2023 theorem also cannot be invoked with "\(d=4\)" merely because
\(d_{n,j}=O(n^4)\).  Its denominator is \(n^4\), whereas the BBP denominator
is a product of four distinct affine functions.  Moreover, even the formal
choice \(a=5,d=4\) violates
\(\operatorname{rad}(4)\mid\operatorname{rad}(5)\), and the actual modular
base is (1), not 5.

The transfer ledger is therefore:

| required hypothesis | literature object | BBP object | verdict |
|---|---|---|---|
| fixed integer/algebraic-integer base | \(a\ge2\), or Pisot/Salem \(\alpha\) | \(R=5/2^{27}\), interpreted separately in every odd residue ring | fails |
| denominator tied to exponent index | \(n\) or literal \(n^d\), exponent \(n\) or \(f(n)\) | exponent \(n+1\), modulus \(An+B\) or a product of four such factors | fails |
| free index construction | special indices such as \(n=pq\), \(n=pa^s\), or all \(n\) | the same \(n\) simultaneously fixes seven phases and the moving dyadic depth | fails |
| one scalar fractional part | one \(a^{f(n)}/n^d\) or \(Q(\alpha^n)/n\) | a correlated sum of seven phases, or the 28 pieces in (14) | insufficient |
| conclusion needed | scalar density/discrepancy/interval coverage | target hitting after the state-dependent recurrence (3) | insufficient even if granted |

## 3. What partial fractions really buy

Write

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}.                       \tag{6}
\]

The exact BBP partial fraction is

\[
 \begin{aligned}
 a(k)
 &=\frac4{8k+1}-\frac2{8k+4}-\frac1{8k+5}-\frac1{8k+6}\\
 &=\frac4{8k+1}-\frac1{2(2k+1)}
   -\frac1{8k+5}-\frac1{2(4k+3)}.                  \tag{7}
 \end{aligned}
\]

For \(k=7n+j\), put

\[
 s_{n,j}=5^{n+1}16^{7-j},\qquad M_n=2^{27(n+1)}.   \tag{8}
\]

Then the forcing numerator is

\[
 b_n=\sum_{j=1}^7s_{n,j}a(7n+j).                   \tag{9}
\]

For \(j\le6\), all four terms in (7), after multiplication by
\(s_{n,j}\), are two-adically integral fractions with odd linear
denominators:

\[
 \frac{4s}{8k+1},\quad
 -\frac{s/2}{2k+1},\quad
 -\frac{s}{8k+5},\quad
 -\frac{s/2}{4k+3}.                                \tag{10}
\]

For \(j=7\), however, \(s=5^{n+1}\) is odd.  The second and fourth
formal terms have two-adic valuation \(-1\), so neither has a residue modulo
\(M_n\) as written.  Put \(A=2k+1\) and \(B=4k+3=2A+1\).  Their sum first
pairs, and then splits again with integer numerators:

\[
 \begin{aligned}
 -\frac{s}{2A}-\frac{s}{2B}
 &=-\frac{s(3k+2)}{AB}\\
 &=-\frac{s(k+1)}A+\frac{s(2k+1)}B.              \tag{11}
 \end{aligned}
\]

Indeed, after multiplication by \(AB\), the last equality is just
\((2k+1)^2-(k+1)(4k+3)=-(3k+2)\).  This identity is the point missed by the
naive \(26+1\) split: uniqueness of the constant-coefficient partial
fraction expansion does not prohibit an \(n\)-dependent integer-numerator
recombination.  Equation (11) proves (2) with no parity coupling left.

For any one of the resulting 28 two-integral pieces \(u/L\), define

\[
 \rho\equiv uL^{-1}\pmod {M_n},\quad0\le\rho<M_n,
 \qquad H=\frac{L\rho-u}{M_n}.                     \tag{12}
\]

Then

\[
 \frac{\rho}{M_n}=\frac H L+\frac{u}{LM_n}.        \tag{13}
\]

Also \(H\equiv-uM_n^{-1}\pmod L\), with
\(M_n^{-1}=2^{-27(n+1)}\pmod L\).  This fixes every control sign below.

The signs and fixed coefficients in the 28 linear congruences are explicit.
Writing \(e_j=4(7-j)\), equation (12) gives

| range and pole | integral piece \(u/L\) | lift congruence \(H\pmod L\) |
|---|---|---|
| \(1\le j\le6\), \(8k+1\) | \(4s/(8k+1)\) | \(-4\,2^{e_j}R^{n+1}\) |
| \(1\le j\le6\), \(2k+1\) | \(-(s/2)/(2k+1)\) | \(+2^{e_j-1}R^{n+1}\) |
| \(1\le j\le6\), \(8k+5\) | \(-s/(8k+5)\) | \(+2^{e_j}R^{n+1}\) |
| \(1\le j\le6\), \(4k+3\) | \(-(s/2)/(4k+3)\) | \(+2^{e_j-1}R^{n+1}\) |
| \(j=7\), \(8k+1\) | \(4s/(8k+1)\) | \(-4R^{n+1}\) |
| \(j=7\), \(2k+1\) | \(-s(k+1)/(2k+1)\) | \(+\tfrac12R^{n+1}\) |
| \(j=7\), \(8k+5\) | \(-s/(8k+5)\) | \(+R^{n+1}\) |
| \(j=7\), \(4k+3\) | \(+s(2k+1)/(4k+3)\) | \(+\tfrac12R^{n+1}\) |

Here each congruence has the denominator in the middle column as its
modulus.  For the two recombined rows,
\(2(k+1)=(2k+1)+1\) and \(2(2k+1)=(4k+3)-1\), so the displayed
\(+1/2\) coefficients, including their signs, follow directly from
\(H\equiv-uM_n^{-1}\pmod L\).

Linearity of reduction in \(\mathbb Z/2^{27(n+1)}\mathbb Z\) therefore
gives the exact alternative forcing formula

\[
 \Gamma_n=\left\{
    \sum_{t=1}^{28}\frac{H_t}{L_t}
    +\frac{b_n}{M_n}
 \right\}.                                        \tag{14}
\]

This replaces all seven quartic denominators by odd linear ones.  It is
genuine simplification, but no checked density theorem has the simultaneous,
selected-root shape of (14).

The 28 formal linear functions are

\[
 \begin{array}{ll}
 14n+2j+1,&28n+4j+3,\\
 56n+8j+1,&56n+8j+5,
 \end{array}\qquad 1\le j\le7.                    \tag{15}
\]

Four are not even primitive:

\[
 \begin{array}{rclcrcl}
 28n+7&=&7(4n+1),&&56n+21&=&7(8n+3),\\
 14n+7&=&7(2n+1),&&56n+49&=&7(8n+7).
 \end{array}                                      \tag{16}
\]

In particular, a proof that first requires every linear modulus to be prime
cannot cover all 28 coordinates.

## 4. Why CRT does not split the original seven residues

Within one quartic denominator, abbreviate

\[
 A=2k+1,\quad B=4k+3,\quad C=8k+1,\quad D=8k+5.   \tag{17}
\]

Direct Euclidean calculation gives

\[
 \begin{array}{c|cccccc}
 \text{pair}&(A,B)&(A,C)&(A,D)&(B,C)&(B,D)&(C,D)\\ \hline
 \gcd&1&\gcd(A,3)&1&\gcd(B,5)&1&1.
 \end{array}                                      \tag{18}
\]

Thus \(A,C\) share 3 whenever \(k\equiv1\pmod3\), and \(B,C\) share 5
whenever \(k\equiv3\pmod5\).  Both happen infinitely often in every
seven-phase family.  There is no uniform four-factor CRT.

Even in a coprime instance, if \(d=\prod_rL_r\) and \(h_r=h\bmod L_r\),
CRT yields

\[
 \frac hd\equiv
 \sum_r\frac{h_r\,(d/L_r)^{-1}\bmod L_r}{L_r}\pmod1. \tag{19}
\]

The weights in (19) depend on all the other factors and on \(n\).  This is
not a sum of fixed-base \(a^n/L_r\) sequences.  When (18) is nontrivial,
residues modulo the individual factors do not even retain the extra
3-adic or 5-adic information present in their product.

## 5. The exact prime-binomial adaptation target

The 28 linear lift phases in (14) all have the form

\[
 H_n\equiv C R^{n+1}\pmod {L(n)},qquad
 L(n)=An+B,\quad A\in\{14,28,56\},                 \tag{20}
\]

where \(C\ne0\) is a fixed signed dyadic rational and \(R\) is (1).
The only nonintegral coefficient is \(C=1/2\) in the two recombined rows;
all these modular rationals are defined because every \(L(n)\) is odd.

There is no fixed integer \(a\) that represents \(R\) for all these
moduli.  If \(a\equiv5\,2^{-27}\pmod{L(n)}\) for infinitely many \(n\),
then the unbounded integers \(L(n)\) all divide the fixed integer
\(2^{27}a-5\).  It would follow that \(2^{27}a=5\), impossible for
\(a\in\mathbb Z\).  Hence the fixed-integer-base hypothesis cannot be
restored by choosing representatives.

There is nevertheless an exact reformulation on prime values of \(L\).
If \(p=L(n)\) is prime and \(p\nmid10\), rational Fermat gives

\[
 \begin{aligned}
 H_n^A
 &\equiv C^A R^{A(n+1)}
  =C^A R^{p+A-B}\\
 &\equiv C^A R^{A-B+1}\pmod p.                    \tag{21}
 \end{aligned}
\]

The right side is independent of \(n\).  So \(H_n/p\) is a distinguished
normalized root of the fixed binomial

\[
             Y^A-C^AR^{A-B+1}\pmod p.              \tag{22}
\]

This is the most concrete working stone produced by the application audit.
It also identifies the missing result accurately:

- Hooley-type and Kowalski--Soundararajan results average **all** roots over
  all or typical composite moduli, not the root selected by (20).
- For prime moduli, the Kowalski--Soundararajan introduction says that
  higher-degree polynomial-root equidistribution remains outstanding in
  general; their cited established prime result is quadratic.  The degrees
  in (22) are 14, 28, and 56.
- Four forms in (16) have no unbounded prime values before removing a fixed
  factor 7.
- A scalar theorem for one root coordinate would still not give the joint
  distribution of the 28 coordinates occurring at the same \(n\).

For a composite \(L(n)\), let \(p\mid L(n)\) and \(q=L(n)/p\).  The same
calculation gives only

\[
 H_n^A\equiv C^A R^{q+A-B}\pmod p,                 \tag{23}
\]

whose right side depends on the complementary cofactor \(q\).  Therefore
the local allowed set is not a fixed set \(A_p\) depending only on \(p\), as
required by the checked CRT theorem.  Moreover our sequence chooses one
residue rather than taking the uniform measure on all members of such a
set.  This is an exact hypothesis failure, not merely a missing estimate.

## 6. Marginal density would not control the phase sum

Suppose, beyond the checked literature, that every one of the 28 linear
coordinates in (14) were dense.  This would still not prove that their sum
is dense: two dense coordinates can be perfectly correlated as
\(y_n\) and \(-y_n\), with constant sum.  What is needed is joint control,
for example cancellation of every nonzero vector Weyl sum for the entire
phase vector.  None of the scalar theorems in Section 2 supplies this.

The small term \(b_n/M_n\to0\) is not the obstacle.  Once a suitable
joint density or shrinking-target statement for the modular sum existed,
the vanishing perturbation could be absorbed.  The missing fact is precisely
that joint statement.

## 7. Even excellent forcing coverage does not propagate through (3)

Unrolling (3) from \(m\) to \(N\) gives

\[
 X_N=\left\{10^{N-m}X_m+
       \sum_{r=m}^{N-1}10^{N-1-r}\Gamma_r\right\}. \tag{24}
\]

Thus target hitting depends on correlations between the state and a whole
weighted forcing block, not on the one-dimensional range of
\((\Gamma_n)\).

Here is an exact separator.  Let \(r_k\) be the base-two van der Corput
sequence, so its first \(2^m\) points are exactly

\[
             0,\frac1{2^m},\ldots,\frac{2^m-1}{2^m}             \tag{25}
\]

in some order.  Define

\[
 \begin{array}{lll}
 Y_{2k}=0,&Y_{2k+1}=r_k/10,\\
 \Delta_{2k}=r_k/10,&\Delta_{2k+1}=\{-r_k\}.
 \end{array}                                                   \tag{26}
\]

Then, exactly,

\[
                  Y_{n+1}=\{10Y_n+\Delta_n\}.                  \tag{27}
\]

Every state lies in \([0,1/10)\), so the state never enters, for example,
\([1/5,3/10]\).  On the other hand, the odd forcing subsequence
\(\{\Delta_{2k+1}\}\) is the reflected van der Corput sequence and is
uniformly distributed.  One elementary proof partitions every initial
segment, using the binary expansion of its length, into at most
\(1+\log_2N\) translated dyadic grids; its discrepancy is therefore
\(O((\log N)/N)\).  More strongly for the present purpose, among the first
\(N\) forcing terms the embedded largest complete dyadic grid has circular
mesh less than \(4/N\).  Consequently, for every fixed \(c>0\) and all sufficiently
large \(N\), those forcing terms hit every interval of length
\(cN^{-0.475}\), a weaker demand than their actual mesh bound.

So neither a uniformly distributed forcing subsequence (the 2013 Theorem 1
shape) nor the 2013 shrinking-interval coverage shape implies state target
hitting through (3).  A successful continuation must prove a conditional or
joint theorem involving \(X_n\), or directly estimate the weighted block in
(24).  The separator says nothing negative about the exact BBP correlations;
those correlations are precisely the remaining possible source of a proof.

## 8. Replay and research boundary

The companion
[checker](bbp_fractional_parts_density_application_audit_20260813_check.py)
verifies:

- 257 exact instances of the four-pole identity (7);
- the 28 distinct linear forms, the four fixed factors in (16), and 500
  instances of every gcd identity in (18);
- at 18 depths, the exact 28-formal-term sum, the two nonintegral terms, the
  Bézout recombination (11), and the resulting 28-linear dyadic lift back to
  \(\Gamma_n\), including 504 exact lift identities and all 504 control
  signs in the table above;
- 3,798 prime instances of the binomial-root identity (21);
- the dyadic-grid property of ten van der Corput blocks and 2,048 exact
  transitions of the recurrence separator.

Replay from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_check.py
```

The retained output is `status: PASS`, with
`cklrs_directly_applies: false`,
`dubickas_n_power_d_directly_applies: false`,
`scalar_forcing_density_implies_state_hitting: false`, and
`asserts_v1: false`.  This finite replay is an `experiment`, not evidence for
an infinite distribution claim.

The bounded primary-source search on 2026-08-13 covered the cited paper's
forward literature, `a^n/n`, `a^{f(n)}/n^d`, rational bases, affine
denominators, roots of polynomial congruences, and CRT equidistribution.  No
primary theorem was located that controls the distinguished rational-base
root (20) over affine moduli, much less its simultaneous BBP vector.  This
negative search result is dated and bounded, not a claim that no such theorem
can exist.

A repository mathlib search for `equidistribut`, `discrepancy`, and
fractional-part power sequences found no theorem formalizing any of the
needed analytic distribution results.  No Lean file or axiom-audit entry is
added because there is no V1-supporting theorem to register.

This branch registered the descendant-area watch
`watch:local:pi-digits:fractional-parts-an-over-n-audit-20260813` on
`local:pi-digits` for agent `codex-an-over-n-auditor`.  Its latest poll was
empty at cursor and delivered sequence 57,224, so no event was acknowledged.
Observation events were not used as mathematical evidence.

## Sharp handoff

The 2013 and 2023 density results do not bridge the BBP diagonal.  The
partial-fraction idea nevertheless improves the exact endpoint from seven
quartic phases to (14), and prime values of its 28 linear pieces satisfy the
fixed-binomial relation (21).  A viable literature or new-proof attack would
need all three of the following, not merely a scalar density theorem:

1. distribution of the **selected** roots in (20), including composite
   affine moduli where the local target varies as in (23);
2. joint cancellation for the 28 linear coordinates at a common index
   \(n\);
3. a conditional/block estimate strong enough to control (24), rather than
   only the marginal distribution of \(\Gamma_n\).

No checked source supplies any one of these in the required form.  This is a
more precise obstruction and a cleaner next target, but it is not a proof of
V1.
