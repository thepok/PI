# Gauss--Lambert all-depth two-adic edge

**Status:** `proof sketch`, with an exact finite checker.  This closes the
two-primary subproblem left as conjecture (35) in
[`gauss_exceptional_gcd_upper_bound_attack.md`](gauss_exceptional_gcd_upper_bound_attack.md),
subject to independent line-by-line review.  It does **not** close the
varying odd-prime zero-set term, prove a decimal-cylinder hit, or prove V1.

Search and derivation date: **2026-08-12 UTC**.

## 1. Result

Let

\[
 Q_0=Q_1=1,\qquad
 Q_n=(2n-1)Q_{n-1}+(n-1)^2Q_{n-2}\quad(n\ge2).                 \tag{1}
\]

Then, for every \(n\ge0\),

\[
 v_2(Q_n)-\lfloor n/2\rfloor=
 \begin{cases}
 0,&n\equiv0,1\pmod4,\\
 1,&n\equiv2\pmod4,\\
 v_2(n+1),&n\equiv3\pmod4.
 \end{cases}                                                   \tag{2}
\]

The only all-depth case in (2) is \(n\equiv3\pmod4\).  The key new
identity is a scaled two-adic isometry.  Put

\[
 c_j=\frac{j!}{(2j+1)!!},\qquad
 F(x)=\sum_{j\ge0}c_j\binom{x}{j}^{\!2}.                       \tag{3}
\]

The series converges for every \(x\in\mathbb Z_2\).  For distinct
nonnegative integers \(s,t\),

\[
 v_2\!\left(F(2t-1)-F(2s-1)\right)=2+v_2(t-s).                 \tag{4}
\]

Moreover,

\[
 F(-1)=\sum_{j\ge0}\frac{j!}{(2j+1)!!}=0\quad\hbox{in }\mathbb Q_2. \tag{5}
\]

Taking \(s=0\) in (4) gives exactly the missing unbounded valuation.

## 2. Correct coefficient normalization

Set \(U_n=Q_n/n!\).  Multiplying (1) by \(x^n/n!\), or directly summing
the recurrence for \(U_n\), gives

\[
 \sum_{n\ge0}\frac{Q_n}{n!}x^n
   =(1-2x-x^2)^{-1/2}.                                        \tag{6}
\]

Consequently

\[
 Q_n=\sum_{k=0}^{\lfloor n/2\rfloor}
 \frac{(n!)^2}{2^k(k!)^2(n-2k)!}.                             \tag{7}
\]

This also gives the exact generalized-central-trinomial relation

\[
 Q_n=\frac{n!}{2^n}[X^n](1+2X+2X^2)^n.                       \tag{8}
\]

Equations (6)--(8), rather than the discarded Lagrange parametrization from
an earlier false start, are used throughout this report.

## 3. The even indices

Put \(n=2m\) in (7), reverse the summation index, and remove the odd unit
\(((2m-1)!!)^2\).  One obtains

\[
 Q_{2m}=2^m((2m-1)!!)^2K_m,
 \qquad
 K_m=\sum_{j=0}^m\frac{j!\binom mj^2}{(2j-1)!!},              \tag{9}
\]

where \((-1)!!=1\).  Since \(v_2(j!)\ge1\) for \(j\ge2\), reduction
modulo two gives

\[
 K_m\equiv1+m^2\pmod2.                                       \tag{10}
\]

Thus \(K_m\) is odd when \(m\) is even.  If \(m\) is odd, terms with
\(j\ge4\) vanish modulo four and

\[
 K_m\equiv
 1+m^2+2\binom m2^2+2\binom m3^2\pmod4.                      \tag{11}
\]

For odd \(m\), \(\binom m2\) and \(\binom m3\) have the same parity:
over \(\mathbb F_2\), their quotient is \((m-2)/3=1\) whenever the
first is nonzero, and the assertion is also immediate from the last two
binary digits of \(m\).  Hence (11) is \(2\pmod4\).  It follows that

\[
 v_2(Q_{2m})=
 \begin{cases}m,&m\text{ even},\\m+1,&m\text{ odd}.
 \end{cases}                                                  \tag{12}
\]

## 4. The odd indices and the endpoint null identity

Putting \(n=2m+1\) in (7) gives

\[
 Q_{2m+1}=2^m((2m+1)!!)^2H_m,
 \qquad
 H_m=\sum_{j=0}^m\frac{j!\binom mj^2}{(2j+1)!!}.              \tag{13}
\]

Thus \(H_m=F(m)\).  If \(m\) is even, (3) modulo two contains only the
terms \(j=0,1\), and

\[
 H_m\equiv1+\frac{m^2}{3}\equiv1\pmod2.                      \tag{14}
\]

For odd \(m\), the endpoint \(x=-1\) matters.  Since
\(\binom{-1}{j}=(-1)^j\), equation (5) says \(F(-1)=0\).  Here is a
direct two-adic proof of that endpoint identity.

First,

\[
 c_j=\frac{2^j(j!)^2}{(2j+1)!}
     =\int_0^1\bigl(2z(1-z)\bigr)^j\,dz.                      \tag{15}
\]

The integral in (15) is ordinary coefficientwise antiderivative evaluation,
so the equality is the beta-integral identity between rational numbers.  On
the closed two-adic unit disk, \(z(1-z)\in2\mathbb Z_2\), hence
\(2z(1-z)\in4\mathbb Z_2\).  The geometric series and its
coefficientwise antiderivatives therefore converge uniformly: integration
can lose at most \(\lfloor\log_2(2j+1)\rfloor\) powers of two from the
\(2^j\) in the \(j\)-th summand.  Consequently

\[
 \sum_{j\ge0}c_j
 =\int_0^1\frac{dz}{1-2z(1-z)}.                               \tag{16}
\]

Work in \(K=\mathbb Q_2(i)\), with the valuation normalized by
\(v_2(2)=1\).  Since \((1+i)(1-i)=2\), conjugation gives

\[
 v_2(1+i)=v_2(1-i)=\frac12.                                  \tag{17a}
\]

Therefore the usual local series
\(\operatorname{Log}_2(1+w)=\sum_{r\ge1}(-1)^{r+1}w^r/r\)
converges after substituting either \(w=-(1-i)z\) or
\(w=-(1+i)z\) on the unit disk.  Its tails tend uniformly to zero there:
the \(r\)-th term has valuation at least
\(r/2-v_2(r)\to\infty\).  The denominator factors as

\[
 1-2z+2z^2=(1-(1+i)z)(1-(1-i)z).                              \tag{17}
\]

The exact partial fractions are

\[
 \frac1{1-2z+2z^2}
 =\frac{(1-i)/2}{1-(1+i)z}
  +\frac{(1+i)/2}{1-(1-i)z}.                                  \tag{18}
\]

Integrating the two crossed summands in (18) gives the primitive

\[
 \frac{i}{2}\left(
   \operatorname{Log}_2(1-(1+i)z)
  -\operatorname{Log}_2(1-(1-i)z)
 \right).                                                     \tag{18a}
\]

At \(z=0\), both logarithms are \(\operatorname{Log}_2(1)=0\).  At
\(z=1\), their arguments are \(-i\) and \(i\), respectively.  Both lie in
the convergence disk (their differences from one are associates of
\(1-i\)).  The displayed local logarithm is additive on
\(1+\mathfrak m_K\).  Since \(\pm i\) belong to that group and have order
four, additivity gives
\(4\operatorname{Log}_2(\pm i)=\operatorname{Log}_2(1)=0\), so both
logarithms vanish in the characteristic-zero field \(K\).  Equations
(16)--(18a) prove (5).  Notice the sharp real/two-adic distinction: the same
rational partial sums converge to \(\pi/2\) over \(\mathbb R\), but to zero
over \(\mathbb Q_2\).

## 5. Pairing proves the scaled isometry

We use one elementary binomial Lipschitz estimate.  For integral \(a,b\)
and \(k\ge1\),

\[
 v_2\!\left(\binom ak-\binom bk\right)
 \ge v_2(a-b)-\lfloor\log_2 k\rfloor.                         \tag{19}
\]

Indeed, Vandermonde writes the difference as
\(\sum_{h=1}^k\binom{a-b}{h}\binom b{k-h}\), while

\[
 \binom{a-b}{h}=\frac{a-b}{h}\binom{a-b-1}{h-1}
\]

has valuation at least \(v_2(a-b)-v_2(h)\).  This also covers negative
upper arguments because generalized integral binomial coefficients remain
integers.

For \(r,t\ge0\), pair terms \(2r\) and \(2r+1\) in (3):

\[
 \Psi_r(t)=c_{2r}\binom{2t-1}{2r}^{\!2}
           +c_{2r+1}\binom{2t-1}{2r+1}^{\!2}.                 \tag{20}
\]

Using

\[
 \frac{c_{2r+1}}{c_{2r}}=\frac{2r+1}{4r+3},\qquad
 \binom{x}{2r+1}=\binom{x}{2r}\frac{x-2r}{2r+1},             \tag{21}
\]

one gets the exact factorization

\[
 \Psi_r(t)=
 \frac{2(2r)!}{(4r+1)!!(2r+1)(4r+3)}
 \binom{2t-1}{2r}^{\!2}M_r(t),                               \tag{22}
\]

where

\[
 M_r(t)=6r^2-4rt+7r+2t^2-2t+2.                               \tag{23}
\]

Let \(d=t-s\ne0\).  Equation (19), applied to
\(\binom{2t-1}{2r}\), loses at most
\(\lfloor\log_2(2r)\rfloor\) powers of two, while

\[
 M_r(t)-M_r(s)=2d(t+s-2r-1).                                  \tag{24}
\]

Write (22) as \(\Psi_r(t)=A_rB_r(t)^2M_r(t)\), where
\(B_r(t)=\binom{2t-1}{2r}\).  The prefactor has
\(v_2(A_r)=1+v_2((2r)!)\), since all its remaining factors are odd.  The
difference expands as

\[
 \Psi_r(t)-\Psi_r(s)
 =A_r\bigl((B_r(t)^2-B_r(s)^2)M_r(t)
          +B_r(s)^2(M_r(t)-M_r(s))\bigr).                    \tag{24a}
\]

All the displayed binomial values and \(M_r\)-values are integers.  By
(19), applied to upper arguments whose difference is \(2d\),

\[
 v_2(B_r(t)-B_r(s))
 \ge1+v_2(d)-\lfloor\log_2(2r)\rfloor.                       \tag{24b}
\]

Since \(B_r(t)^2-B_r(s)^2\) contains that difference, the first term in
parentheses in (24a) has at least the valuation in (24b).  By (24), the
second term has valuation at least \(1+v_2(d)\), which is no smaller.
Adding \(v_2(A_r)\) therefore gives

\[
 v_2(\Psi_r(t)-\Psi_r(s))
 \ge v_2(d)+2+v_2((2r)!)-\lfloor\log_2(2r)\rfloor.            \tag{25}
\]

For \(r\ge2\),
\(v_2((2r)!)\ge\lfloor\log_2(2r)\rfloor+1\): check \(r=2\)
directly, and for \(r\ge3\) the \(r\) even factors already suffice.
Thus

\[
 v_2(\Psi_r(t)-\Psi_r(s))\ge v_2(d)+3\qquad(r\ge2).           \tag{26}
\]

It remains to retain one bit from the first two pairs.  They are

\[
 \Psi_0(t)=1+\frac{(2t-1)^2}{3},                              \tag{27}
\]

and

\[
 \Psi_1(t)=\frac4{315}G(t),\qquad
 G(t)=((2t-1)(t-1))^2(2t^2-6t+15).                            \tag{28}
\]

Hence

\[
 \frac{\Psi_0(t)-\Psi_0(s)}{4d}
   =\frac{t+s-1}{3}\equiv t+s-1\pmod2.                       \tag{29}
\]

As a polynomial, \(G(X)\equiv X^2+1\pmod2\), so its divided difference
satisfies

\[
 \frac{\Psi_1(t)-\Psi_1(s)}{4d}
 =\frac{G(t)-G(s)}{315d}\equiv t+s\pmod2.                    \tag{30}
\]

Equations (26), (29), and (30) show that the full quotient is odd:

\[
 \frac{F(2t-1)-F(2s-1)}{4(t-s)}\equiv1\pmod2.                \tag{31}
\]

The series in (31) converges because \(v_2(c_j)=v_2(j!)\to\infty\).
This proves the exact isometry (4).

Now let \(m=2t-1\ge1\).  From (5) and (4),

\[
 v_2(H_m)=v_2(F(2t-1)-F(-1))
 =2+v_2(t)=1+v_2(m+1).                                       \tag{32}
\]

Combining (12)--(14) and (32) proves (2).

## 6. Consequence for the exceptional gcd

The preceding exceptional-gcd audit established

\[
 v_2(E_n)\le v_2(Q_n)-\lfloor n/2\rfloor.                    \tag{33}
\]

Equation (2) now turns the right-hand side into \(O(\log n)\).  Thus the
prime two contributes only \(o(n)\) to \(\log E_n\).  The remaining
obstruction in that route is exactly the varying odd-prime root contribution

\[
 \sum_{\sqrt n<\ell<n\atop U_{n\bmod\ell}\equiv0\pmod\ell}\log\ell,
\]

not a hidden two-primary term.

## 7. Literature check

This bounded search is `literature-checked` as of **2026-08-12 UTC**.

- Tony D. Noe,
  [*On the Divisibility of Generalized Central Trinomial Coefficients*,
  J. Integer Sequences 9 (2006), Article 06.2.7](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf),
  records the generating function and Legendre/generalized-trinomial
  framework containing \([X^n](1+2X+2X^2)^n\).  The pinned PDF SHA-256 in
  the preceding audit is
  `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c`.
  Noe's paper supplies the already-audited odd-prime Lucas prior art; it does
  not state (2).
- [OEIS A012244](https://oeis.org/A012244) records (1), (6), (8), and the
  word-count interpretation of \(Q_n\).  [OEIS A006139](https://oeis.org/A006139)
  records the generalized central trinomial sequence in (8).  These entries
  are provenance and cross-checks, not substitutes for the derivation above.
- The reviewed [LMFDB entry on the p-adic logarithm](https://www.lmfdb.org/knowledge/show/lf.log)
  records the extension of \(\log_p\) by zero on roots of unity, the only
  p-adic-log property used in (18).

Queries included variants of “A012244 2-adic valuation,” “A006139 2-adic,”
“generalized central trinomial coefficient valuation,” and the exact initial
terms.  No checked source was found that states (2) or (4).  Absence from
this bounded search is not a novelty claim.

## 8. Exact replay

Run

```bash
python work/ultrapi-resume/gauss_two_adic_all_depth_check.py
```

Expected output:

```text
PASS: exact Q/coefficient normalizations, the mod-4 valuation law through n=512, 2016 odd-shadow isometry pairs, and 17160 paired-term divisibility checks
EXPERIMENT: endpoint partial-sum valuations at N=2^k-1 are 1:2, 3:5, 7:10, 15:19, 31:36, 63:69, 127:134
```

The checker uses exact integers and rational numbers.  It checks (1), (7),
(9), (13), (20)--(22), the finite isometry shadows, and (2) through
\(n=512\).  Its endpoint row is only finite evidence; the proof of the
infinite endpoint value is (15)--(18a).

## 9. Handoff

This report upgrades the two-adic formula from `conjecture` to a
`proof sketch`.  It should receive an independent normalization and
p-adic-endpoint audit before the parent dossier treats it as settled.  Even
after that audit, the Gauss--Lambert route does not prove V1: the odd-prime
\(U_s\)-zero aggregate remains open.
