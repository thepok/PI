# Restricted-denominator attack: Iyer's 0/1 denominators versus the fixed return

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No decimal cylinder hit or proof that every finite decimal word occurs in pi
was obtained.  Canonical V1 remains a `conjecture`.

The bounded source search is `literature-checked` as of the audit date.
Iyer's theorem gives a genuine unconditional approximation statement for pi:
there are unbounded *displayed* denominators \(q\) whose decimal digits are
all 0 or 1 and for which

\[
                 q\left|\pi-\frac aq\right|\longrightarrow0.       \tag{1}
\]

The fraction in (1) need not be in lowest terms, so its reduced denominator
may be a proper divisor of \(q\).  This is exactly the right *Archimedean
scale* for a fixed-multiplier return,
but it uses the wrong denominator language.  Iyer's selected denominator is
an arbitrary subset sum of powers of ten; the needed denominator is
\(10^N-c\), or a sufficiently large divisor of it with a controlled
cofactor.  The paper supplies no divisibility, multiplicative-order, or
discrete-log control of that kind.

There is a route-closing `proof sketch` obstruction at Iyer's proved
\(N^{-2}\) scale.  Every rational number admitting a decimal expansion using
only 0 and 1 has equal 2-adic and 5-adic exponents in its reduced
denominator.  Combining this fact with Schleischitz's published extrinsic
distance theorem for missing-digit Cantor sets shows that if \(d\) has only
decimal digits 0 and 1 and

\[
                         kd=10^N-16,                                \tag{2}
\]

then, for every \(N\geq5\),

\[
             \boxed{k>N^2},\qquad
             k>\frac{(N-\log_{10}32)^{\log_2 10}}{20}.              \tag{3}
\]

In fact the second bound in (3) gives

\[
                         \frac{k}{N^2}\longrightarrow\infty.        \tag{4}
\]

Consequently, the sufficient transfer condition \(k=o(N^2)\) at Iyer's
stated \(O(N^{-2})\) phase scale is impossible for every aligned 0/1
denominator.  This closes that proposed use of Iyer's theorem.  It does not
close the exact divisor-return condition: an aligned denominator could in
principle have phase much smaller than the bound guaranteed by Iyer, namely
\(\|d\pi\|=o(1/k)\).  No checked source provides such exceptional fixed-pi
cancellation.  The companion finite replay is an `experiment`; nothing here
is a `candidate resolution`.

## 1. Exact return criterion

Let

\[
 K_{10}(x)=\overline{\{10^n x\bmod1:n\geq0\}}\subset\mathbb T.
\]

The independently audited Furstenberg bridge in
[`furstenberg_bbp_bridge.md`](furstenberg_bbp_bridge.md) gives

\[
 \mathrm{V1}
 \Longleftrightarrow16\pi\in K_{10}(\pi)
 \Longleftrightarrow
 \liminf_{N\to\infty}\|(10^N-16)\pi\|_{\mathbb T}=0.               \tag{5}
\]

Equivalently, along an unbounded subsequence there must be rationals
\(a_N/(10^N-16)\) with

\[
 \left|\pi-\frac{a_N}{10^N-16}\right|=o(10^{-N}).                  \tag{6}
\]

A divisor version is possible.  If \(d_N\mid10^N-16\), put
\(k_N=(10^N-16)/d_N\).  Then

\[
 \|(10^N-16)\pi\|_{\mathbb T}
 =\|k_N(d_N\pi)\|_{\mathbb T}
 \leq k_N\|d_N\pi\|_{\mathbb T}.                                 \tag{7}
\]

Consequently, a small phase on \(d_N\) transfers only after paying the whole
cofactor \(k_N\).  This cofactor is the arithmetic quantity missing from an
unrestricted denominator theorem.

## 2. What Iyer's theorem actually supplies

For an integer base \(b\geq2\), define

\[
 \mathfrak D_b=
 \left\{\sum_{j\geq0}\varepsilon_jb^j:
   \varepsilon_j\in\{0,1\},\quad
   0<\sum_j\varepsilon_j<\infty\right\}.
\]

Here the sum is finite by definition.  Equivalently, \(\mathfrak D_b\) is
the set of positive integers whose ordinary base-\(b\) expansion has only
digits 0 and 1.  Leading zeros change nothing, and no restriction is imposed
on the units digit.  The integer \(q\) itself, rather than necessarily the
reduced denominator after cancelling \(a/q\), is the restricted object.

Iyer's Theorem 1.1, checked in the open arXiv source, states that for every
real \(\gamma\) and all sufficiently large integer cutoffs \(X\),

\[
 \min_{\substack{1\leq q\leq X\\q\in\mathfrak D_b}}
       \|q\gamma\|_{\mathbb T}
 \leq \frac{C_b}{(\log X)^2},                                     \tag{8}
\]

where \(C_b\) is effective and depends only on \(b\).  The source's stated
Vinogradov convention explicitly makes the implied constant independent of
both \(X\) and \(\gamma\); in particular it is uniform at the fixed input
\(\gamma=\pi\).  The result was
published as Siddharth Iyer,
[*Rational approximation with digit-restricted denominators*](https://doi.org/10.1093/qmath/haaf007),
*Quarterly Journal of Mathematics* **76** (2025), 381--394; the theorem was
checked against [arXiv:2312.01076v1](https://arxiv.org/abs/2312.01076).

Apply (8) with \(b=10\), \(\gamma=\pi\), and \(X\to\infty\).  A finite set
of denominators cannot make \(\|q\pi\|\) tend to zero, since pi is
irrational.  Hence the selected \(q\)'s are unbounded.  If \(a\) is a nearest
integer to \(q\pi\), then

\[
 \left|\pi-\frac aq\right|
 \leq\frac{C_{10}}{q(\log X)^2}=o(q^{-1}),                         \tag{9}
\]

which proves (1), with \(q\) understood as the displayed denominator.  The
power \((\log X)^{-2}\) is exact; the theorem does not contain an omitted
power of \(X\) or \(q\).

The quantifier mismatch is exact:

- \(\mathfrak D_{10}\) has \(2^N-1\) positive members below \(10^N\), and
  Iyer's exponential-sum proof averages over this subset-sum family.
- For fixed positive \(c\), the decimal expansion of \(10^N-c\) has a long
  prefix of 9s once \(N\) exceeds the length of \(c\).  Therefore
  \(10^N-c\notin\mathfrak D_{10}\) for all sufficiently large \(N\).
- A divisor \(d\in\mathfrak D_{10}\) can still be used through (7), but
  Iyer's theorem does not select witnesses by divisibility in
  \(10^N-c\), does not control \(10^N\bmod d\), and does not bound the
  complementary quotient.
- It also supplies no annular lower bound such as
  \(d\geq X/(\log X)^A\).  The selected witnesses must go to infinity, but
  they may be arbitrarily small relative to the ambient cutoff \(X\).

There is also a decisive logical separator.  Equation (8) holds for every
real number, including the Liouville number

\[
                    \alpha=\sum_{j\geq1}10^{-j!},                  \tag{10}
\]

whose decimal digits are only 0 and 1 and whose decimal orbit omits every
cylinder containing digit 2.  Thus an Iyer-small subset sum of decimal orbit
points cannot, by itself, imply density of the individual decimal orbit.

## 3. A denominator lemma for the decimal 0/1 Cantor set

Let

\[
 C_{01}=\{0.a_1a_2\ldots:a_j\in\{0,1\}\}\subset[0,1].
\]

**Rational-denominator lemma (`proof sketch`).**  If \(x=p/q\in C_{01}\)
is in lowest terms, then

\[
                              v_2(q)=v_5(q).                        \tag{11}
\]

To see this, write an eventually periodic 0/1 expansion as

\[
 x=0.a_1\cdots a_s\overline{b_1\cdots b_t}.
\]

Let \(A\) and \(B\) be the integers represented by the preperiod and period,
with leading zeros retained conceptually, and put \(U=A10^t+B\), the
concatenation.  Then

\[
 x=\frac{A(10^t-1)+B}{10^s(10^t-1)}
  =\frac{U-A}{10^s(10^t-1)}.                                     \tag{12}
\]

Both \(U\) and \(A\) have only digits 0 and 1.  If they are unequal, let
\(r\) be the first decimal position from the right at which their digits
differ.  Then

\[
 10^r\mid U-A,\qquad (U-A)/10^r\equiv\pm1\pmod {10},             \tag{13}
\]

so \(v_2(U-A)=v_5(U-A)=r\).  The unreduced denominator in (12) has
equal 2- and 5-adic exponents \(s\), because \(10^t-1\) is coprime to ten.
Reduction therefore removes equal powers of 2 and 5 and leaves (11).  The
case \(U=A\) is \(x=0\), and terminating expansions are included by taking
the repeating block to be zero.

The same trailing-digit argument shows that every positive integer whose
decimal digits are only 0 and 1 satisfies

\[
                              v_2(d)=v_5(d),                        \tag{14}
\]

both valuations being the number of trailing zero digits.

## 4. A general cofactor obstruction and the exact c=16 bound

The preceding lemma gives a reusable fixed-multiplier statement.  Fix
\(c\geq1\) with

\[
                         v_2(c)\neq v_5(c),                        \tag{15}
\]

and put \(S_c=\max(v_2(c),v_5(c))\).  Suppose \(N>S_c\),
\(d\in\mathfrak D_{10}\), and

\[
                    10^N-c=kd,\qquad k>c.                         \tag{16}
\]

Unequal-valuation arithmetic and (14) give

\[
 v_p(10^N-c)=v_p(c)\quad(p=2,5),
 \qquad v_2(k)-v_5(k)=v_2(c)-v_5(c)\neq0.                         \tag{17}
\]

On the other hand,

\[
                 \frac{10^N}{k}=d+\frac ck,\qquad0<\frac ck<1,   \tag{18}
\]

so the first \(N\) decimal digits of \(1/k\) are the zero-padded
digits of \(d\), all 0 or 1.  Write

\[
 k=2^a5^b m,\qquad \gcd(m,10)=1,\qquad
 s=\max(a,b)\leq S_c.                                            \tag{19}
\]

If \(m=1\), the expansion terminates; the first \(N\) allowed digits followed
by zeros would put \(1/k\) in \(C_{01}\), contradicting (11) and (17).
Hence \(m>1\).  After the first \(s\) decimal places, the nonterminating part
has period \(t=\operatorname{ord}_m(10)\).  If \(t\leq N-s\), one entire period has
already appeared among the first \(N\) allowed digits; every later digit is
then also 0 or 1.  This contradicts (11) and (17).  Hence

\[
 t>N-s,\qquad t\leq\varphi(m)\leq m-1,\qquad
 k\geq m\geq N-S_c+2.                                             \tag{20}
\]

This is a linear cofactor obstruction for every fixed \(c\) satisfying
(15).  It is not an exclusion when \(v_2(c)=v_5(c)\); for example,
\(c=1\), \(d=(10^N-1)/9\), \(k=9\) is the familiar repunit family.

For the relevant multiplier \(c=16\), the constants sharpen.  For
\(N\geq5\),

\[
 v_2(10^N-16)=4,\qquad v_5(10^N-16)=0.                           \tag{21}
\]

Any divisor \(d\in\mathfrak D_{10}\) must end in 1, hence is odd, so the
cofactor has the exact form \(k=16m\), \(\gcd(m,10)=1\).  If \(k=16\), then

\[
 d=\frac{10^N-16}{16}=625\,10^{N-4}-1,                            \tag{22}
\]

which ends in 9 and is not in \(\mathfrak D_{10}\).  Thus \(m>1\), and
the period argument gives

\[
 \operatorname{ord}_m(10)>N-4,\qquad
 m\geq N-2,\qquad
 k=16m\geq16(N-2).                                               \tag{23}
\]

There is a further exact sharpening from the long-division states.  Assume
\(N\geq8\), and write \(k=16m\) as above.  For \(4\leq i\leq N\), let

\[
 r_i=10^i\bmod k=16s_i,\qquad 1\leq s_i<m.                         \tag{23a}
\]

The first \(N\) digits of \(1/k\) are the zero-padded digits of \(d\), so
they all lie in \(\{0,1\}\).  The next-digit formula for long division
therefore gives

\[
 5r_i<k\quad(4\leq i<N),
 \qquad r_N=16.                                                     \tag{23b}
\]

The preliminary bound \(m\geq N-2\) implies \(m>5\), and hence (23b) says
\(1\leq s_i<m/5\) for every \(4\leq i\leq N\), including the endpoint
\(s_N=1\).  These \(N-3\) states are distinct.  Indeed, if
\(r_i=r_j\) for \(4\leq i<j\leq N\), deterministic long division repeats
the already-seen digit block from positions \(i+1\) through \(j\) forever.
Every digit of \(1/k\) would then be 0 or 1, contradicting the
rational-denominator lemma because \(v_2(k)=4\ne0=v_5(k)\).  There are only
\(\lfloor(m-1)/5\rfloor\) positive integers below \(m/5\), so

\[
 N-3\leq\left\lfloor\frac{m-1}{5}\right\rfloor,
 \qquad m\geq5N-14,
 \qquad \boxed{k\geq80N-224}.                                    \tag{23c}
\]

This elementary proof of (23c) is retained because it is independent of the
published fractal-distance input used next.

### Published Cantor-distance bound closes the quadratic window

Schleischitz's Theorem 3.4, specialized to a missing-digit set
\(C_{b,W}\) of dimension \(\Delta=\log|W|/\log b\), states that every
reduced rational \(p/q\notin C_{b,W}\) satisfies

\[
 \operatorname{dist}\!\left(C_{b,W},\frac pq\right)
 >\frac{b^{-(2b)^\Delta q^\Delta}}{2q}.                            \tag{23d}
\]

Apply (23d) with \(b=10\), \(W=\{0,1\}\),
\(\Delta=\log2/\log10\), and the reduced rational \(1/k\).  It is outside
\(C_{01}\) by the denominator lemma because
\(v_2(k)=4\ne0=v_5(k)\).  On the other hand, (18) gives the explicit nearby
Cantor point \(d/10^N\) and hence

\[
 \operatorname{dist}\!\left(C_{01},\frac1k\right)
 \leq\left|\frac1k-\frac d{10^N}\right|
 =\frac{16}{k10^N}.                                                \tag{23e}
\]

Since \(10^\Delta=2\), we also have
\((2b)^\Delta=20^\Delta\).  Comparing (23d) and (23e) gives

\[
 \frac{16}{k10^N}>
 \frac{10^{-20^\Delta k^\Delta}}{2k},\qquad
 20^\Delta k^\Delta>N-\log_{10}32,
\]

and therefore

\[
 \boxed{
 k>\frac{(N-\log_{10}32)^{1/\Delta}}{20}
   =\frac{(N-\log_{10}32)^{\log_2 10}}{20}.}                       \tag{23f}
\]

In particular, \(k/N^2\to\infty\) along every unbounded aligned family.
The simpler uniform inequality \(k>N^2\) for every \(N\geq5\) follows by
combining three ranges.  For \(5\leq N\leq7\), (23) gives
\(k\geq16(N-2)>N^2\).  For \(8\leq N\leq25\), (23c) gives
\(k\geq80N-224>N^2\).  For \(N\geq26\), use
\(\log_2 10>3\) and \(\log_{10}32<2\) in (23f):

\[
 k>\frac{(N-2)^3}{20}>N^2,
\]

where the last inequality holds at \(N=26\) because
\(24^3=13824>20\cdot26^2=13520\), and
\((N-2)^3/N^2\) is increasing for \(N>2\).  This proves both claims in
(3)--(4).

The same conclusion also follows qualitatively from Schleischitz's Theorem
4.9: if a rational outside \(C_{b,W}\) has its first \(s+1\) base-\(b\)
digits in \(W\), its reduced denominator is \(\gg s^{1/\Delta}\).  For
\(1/k\), the first \(N\) digits are the padded digits of \(d\), giving
\(k\gg(N-1)^{\log_2 10}\).  Formula (23f) records explicit constants and
also checks this theorem's application directly.

The bound does not say that such divisors never exist.  For example, exact
modular calculation gives

\[
 10^{208}\equiv16\pmod {1011},\qquad
 10^{190}\equiv16\pmod {1101},                                  \tag{24}
\]

and both 1011 and 1101 have only 0/1 decimal digits.  Their complementary
quotients are exponential in \(N\), so they are unusable in (7).  These
examples prevent the false stronger claim that digit language alone forbids
all divisors.

## 5. The exact residual theorem needed to exploit Iyer

The exact joint condition needed by the divisor-transfer mechanism is the
existence of \(N_j\to\infty\) and \(d_j\in\mathfrak D_{10}\) such that,
with

\[
 d_j\mid10^{N_j}-16,\qquad
 k_j=\frac{10^{N_j}-16}{d_j},                                    \tag{25}
\]

one has

\[
                         k_j\|d_j\pi\|_{\mathbb T}\longrightarrow0.
                                                                    \tag{26}
\]

Indeed, (7) then gives the fixed return (5).  Condition (26) is the joint
arithmetic--Archimedean input for this method; neither small phase without
alignment nor alignment without small phase is enough.

Take \(X=10^N\) in (8).  Absorbing \((\log10)^{-2}\) into the constant,
Iyer supplies some \(d_N\in\mathfrak D_{10}\), \(d_N\leq10^N\), with

\[
                          \|d_N\pi\|\leq C N^{-2}.                 \tag{27}
\]

This yields the following strongest clean sufficient statement at Iyer's
proved exponent.

**Synchronized-Iyer criterion (`proof sketch`).**  If there are a constant
\(C>0\), integers \(N_j\to\infty\), and \(d_j\in\mathfrak D_{10}\) such
that

\[
 d_j\mid10^{N_j}-16,\qquad
 \|d_j\pi\|_{\mathbb T}\leq C N_j^{-2},\qquad
 k_j=\frac{10^{N_j}-16}{d_j}=o(N_j^2),                            \tag{28}
\]

then \(\|(10^{N_j}-16)\pi\|_{\mathbb T}\leq Ck_j/N_j^2\to0\), so
V1 follows from (5).  However, (4) proves that the cofactor hypothesis in
(28) is impossible for an unbounded aligned family.  Thus the
synchronized-Iyer criterion is a correct implication with inconsistent
arithmetic hypotheses; it cannot be used to prove V1.

There are three distinct quantifiers in (28), and Iyer proves only one of
them.  His theorem at \(X=10^N\) supplies *some* witness satisfying (27),
but it does not assert that this witness

1. ends in 1 (which is necessary to divide \(10^N-16\));
2. lies in the top annulus forced by (28), namely
   \[
       \frac{d_jN_j^2}{10^{N_j}}
       =\left(1-\frac{16}{10^{N_j}}\right)\frac{N_j^2}{k_j}
       \longrightarrow\infty;
   \]
3. satisfies \(10^{N_j}\equiv16\pmod {d_j}\).

Thus the mere size allowance \(d\leq10^N\) is compatible with (28), but it
does not select a suitable \(N\).  One also cannot safely choose \(N\) after
Iyer has selected \(d\).  Such an \(N\) exists only if \(d\) is coprime to
ten and 16 belongs to the cyclic subgroup generated by 10 modulo \(d\); its
least value can be much larger than \(\log_{10}d\).  Changing from the
ambient cutoff used in (27) to that modular exponent destroys the needed
\(N^{-2}\) comparison unless a new synchronization estimate is proved.

At each fixed \(N\), even allowing \(k\leq N^2\) gives only \(O(N^2)\)
possible aligned quotients \(d=(10^N-16)/k\), compared with the
\(2^N\) candidates in Iyer's full digit family up to and including
\(10^N\) (or \(2^N-1\) strictly below it).  Inspection of Iyer's
proof shows that its product exponential sum and discrepancy argument use
that full subset-sum entropy.  No theorem in the paper gives (27) after
restriction to the polynomial-size synchronized subclass in (28).

The stronger cofactor lower bound is now supplied by Schleischitz's
published theorem, so the attempt to transfer Iyer's proved \(N^{-2}\) phase
estimate is closed.  The exact route would require a different input:

> Find aligned \(d_N\in\mathfrak D_{10}\) with
> \(k_N\|d_N\pi\|_{\mathbb T}\to0\), despite
> \(k_N=\Omega(N^{\log_2 10})\).

Such exceptional phase decay is not contradicted by the denominator bound,
but neither Iyer's theorem nor another checked source supplies it.  If
proved, it would already imply V1 through (5).

## 6. Metric approximation is available, but it cannot select pi

There is no scarcity obstruction for a generic real number.  More strongly,
for any sequence of distinct integers \((q_n)\), the sequence
\((q_nx\bmod1)\) is uniformly distributed for Lebesgue-almost every \(x\).
Here is a self-contained `proof sketch`.  For fixed \(h\neq0\), put

\[
 S_M(x)=\frac1M\sum_{n=1}^M e^{2\pi i hq_nx}.
\]

Orthogonality and distinctness give

\[
                  \int_0^1|S_M(x)|^2\,dx=\frac1M.                 \tag{29}
\]

At \(M=j^2\), Chebyshev's inequality with threshold \(j^{-1/4}\) gives a
summable exceptional measure \(j^{-3/2}\).  Borel--Cantelli yields
\(S_{j^2}(x)\to0\) almost everywhere.  The gap between consecutive squares
is \(O(j)\), so direct interpolation gives \(S_M(x)\to0\) for all \(M\).
Intersecting over countably many \(h\neq0\) and applying Weyl's criterion
proves the assertion.

With \(q_n=10^n-16\), almost every \(x\) therefore satisfies the return in
(5).  Weyl's criterion is from
[Weyl, 1916](https://doi.org/10.1007/BF01475864).  This metric result cannot
be specialized to the fixed point \(x=\pi\); its exceptional set includes
explicit irrational points with nondense decimal orbit.  It explains why
probabilistic or almost-everywhere restricted-denominator results are not a
fixed-pi breakthrough.

## 7. E/G-function and irrationality-measure applicability

The nearby special-value literature does not fill (26).

- Schleischitz,
  [*On intrinsic and extrinsic rational approximation to Cantor
  sets*](https://arxiv.org/abs/1812.10689v4), Theorems 3.4 and 4.9,
  supplies the decisive cofactor lower bound (23f).  It closes transfer at
  Iyer's guaranteed \(N^{-2}\) scale, but it is only a denominator-size
  theorem and gives no lower bound for the fixed phase
  \(\|d\pi\|_{\mathbb T}\).
- A fresh 2026 result of Chance Sanford,
  [*A Note on Diophantine Approximation with Restricted
  Denominators*](https://arxiv.org/abs/2606.02620v1), defines positive
  Diophantine density \(\delta\) by the uniform rational-residue estimate
  \[
   \min_{v\in\mathcal A,\ v\leq q}
      \left\|\frac{vp}{q}\right\|\leq Cq^{-\delta}
  \]
  for every sufficiently large reduced \(p/q\).  Its Theorem 3 then gives
  infinitely many \(u/v\), \(v\in\mathcal A\), with error
  \(<v^{-1-\delta+\varepsilon}\).  No positive Diophantine density is known
  for \(\mathfrak D_{10}\), much less for the synchronized set in (28);
  indeed Iyer states positive-power decay for \(\mathfrak D_b\) itself as
  Conjecture 7.1.  Sanford's proved construction applies to complements of
  sparse sets, not to this divisor intersection.
- Chow--Varj\'u--Yu,
  [*Counting rationals and Diophantine approximation in missing-digit
  Cantor sets*](https://arxiv.org/abs/2402.18395v2), proves rational-counting
  and metric approximation results for one-missing-digit sets.  Its main
  Theorems 1.2, 1.4, and 1.8 require \(\#D=b-1\) (apart from their stated
  base-4 cases), so they do not apply to the decimal digit set
  \(D=\{0,1\}\).  They also concern rationals lying in a Cantor set or
  Hausdorff-measure statements, not the fixed-pi phase and divisibility in
  (28).
- Fischler--Rivoal,
  [*Rational approximations to values of E-functions*](https://arxiv.org/abs/2312.12043v2),
  proves irrationality exponent 2 for irrational values of rational-
  coefficient E-functions at rational points.  No checked representation
  puts pi in that class: \(\sin(\pi)=0\) makes pi an input/zero, not an
  E-value at a rational point.
- Their 2026 theorem for real irrational simple zeros of rational-
  coefficient E-functions does apply to pi, but gives only
  \(\lvert\pi-a/b\rvert\geq\exp(-cb^d)\).  This is a lower bound, is far
  below the \(1/b\) return scale, and has no numerator or denominator-
  language restriction.  The exact source audit is in
  [`special_values_digit_complexity_literature.md`](special_values_digit_complexity_literature.md).
- The G-function theorem for fractions with denominator \(B b^m\) is also a
  lower-bound/repetition theorem and its constants require a fixed function
  at a sufficiently small rational point.  It neither creates
  \(10^N-16\) denominators nor proves a selected residue tends to zero.

Even an optimal scalar irrationality exponent for pi would not imply (5):
irrationality measures exclude approximations that are *too good* across all
denominators, whereas (5) asks for an upper approximation along one thin
prescribed sequence.  Denominator selection, not scalar approximation
quality, is the unresolved input.

## 8. Deterministic replay and bounded literature record

The companion
[`restricted_denominator_iyer_attack_check.py`](restricted_denominator_iyer_attack_check.py)
uses exact integer and rational arithmetic.  It checks:

1. the equal 2-/5-adic denominator property for every preperiod/period pair
   of 0/1 blocks through the configured finite exhaustive depth;
2. the exact congruences in (24);
3. the long-division state inequalities and the lower bound (23c) for those
   examples;
4. the exact integer inequalities used to pass from (23), (23c), and (23f)
   to \(k>N^2\) over the three ranges; and
5. as an `experiment`, absence of an aligned quotient with
   \(k\leq N^2\) for \(5\leq N\leq200\).

The fifth item is finite evidence only and has been superseded by the
proof-sketch deduction of \(k>N^2\) for every \(N\geq5\).  It is not evidence
for V1.

Sources checked on **2026-08-12 UTC**:

| source | checked statement | source pin |
|---|---|---|
| [Iyer, arXiv:2312.01076v1](https://arxiv.org/abs/2312.01076v1), published [QJM 76 (2025), 381--394](https://doi.org/10.1093/qmath/haaf007) | Theorem 1.1, equation (8), and the full 0/1 subset-sum denominator family | arXiv e-print SHA-256 `40bacfe7e518c18b116379b900d60053c2e0f64a19cd0049e9d76534c00be183`; PDF SHA-256 `a312fd3c401f46360939dfa7ffff92a3d3f293693a9637fad2f2574e181821d8` |
| [Schleischitz, arXiv:1812.10689v4](https://arxiv.org/abs/1812.10689v4), [*ETDS* **41** (2021), 1560--1589](https://doi.org/10.1017/etds.2020.7) | Theorem 3.4, equation (11), and Theorem 4.9; explicit extrinsic Cantor-distance and prefix-denominator bounds | e-print SHA-256 `28896db4b7dd45b854279f645b08cb4800828d3b8e7df579ea7a299dc304a0c9`; PDF SHA-256 `1bbac7bd2e4d178682b44ded08cd80c9b23883dcaa63423d0592da704a3467e0` |
| [Sanford, arXiv:2606.02620v1](https://arxiv.org/abs/2606.02620v1) | Definition 1 and Theorem 3; positive Diophantine density is an unproved hypothesis for the synchronized set | PDF SHA-256 `4012d480b3c3aff5d2a36c4cc92d2e57027baa9b64454b77edfcaf3b2fb45b0b` |
| [Chow--Varj\'u--Yu, arXiv:2402.18395v2](https://arxiv.org/abs/2402.18395v2), *Adv. Math.* (2026) | Main Theorems 1.2, 1.4, and 1.8; one-missing-digit and metric hypotheses do not cover \(D=\{0,1\}\) or fixed-pi phase alignment | e-print SHA-256 `2d3ddb20cca49fc4e9c3c35b4270aa89d2b5865eab2713a0befda4d12ea41ab5`; PDF SHA-256 `5bb31a65f491bd85a72864938f610cddf04e45bac6e6f635e508ff6cf70b67bf` |
| [Fischler--Rivoal, arXiv:2312.12043v2](https://arxiv.org/abs/2312.12043v2) | Irrationality exponent 2 for irrational E-values at rational points; hypothesis mismatch for pi | e-print SHA-256 `1e01c7b9e7c2d801f941d7d93c6cc66decc2d79570b0db62a8e3e8c9654c93c1`; PDF SHA-256 `d2d8ce8a517ff6836c3f52d2c6ba3a5ce64cdc564d2f3390e8a72524426e2fbc` |
| [Fischler--Rivoal, Math. Ann. 394 (2026), Article 12](https://doi.org/10.1007/s00208-026-03374-z) | Effective lower bound for rational approximation to real irrational simple E-function zeros, specialized to \(\pi\) | independently pinned and page-audited in `special_values_digit_complexity_literature.md` |
| [Weyl, Math. Ann. 77 (1916), 313--352](https://doi.org/10.1007/BF01475864) | Weyl criterion used after the self-contained \(L^2\) metric argument | DOI and journal metadata checked |

## Bottom line

Iyer's theorem reaches the correct \(o(1/q)\) approximation scale for pi,
but on a high-entropy 0/1 denominator family rather than on
\(10^N-16\).  The rational-Cantor denominator lemma plus Schleischitz's
published distance theorem prove
\(k=\Omega(N^{\log_2 10})\), hence \(k/N^2\to\infty\), for every aligned
0/1 divisor family.  This closes the proposed transfer of Iyer's guaranteed
\(N^{-2}\) phase bound.  It does not exclude much smaller exceptional phases
for specially aligned denominators, and no checked theorem supplies those
phases.  V1 therefore remains a `conjecture`.
