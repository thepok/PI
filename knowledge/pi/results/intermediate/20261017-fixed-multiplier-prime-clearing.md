# Fixed-multiplier prime clearing and its five-adic tail cost

Date: 2026-10-17. Labels: `proof sketch` and exact finite `experiment`.
This extends the arithmetic construction in
[PR15 at the reviewed head](https://github.com/thepok/PI/blob/5fd8197ce4a48304392e6c350cee68e29631aaee/knowledge/pi/results/intermediate/20261017-moment-cancelled-positive-carriers.md).
It does not prove a prescribed decimal target hit, CW0, or V1.

## 1. Setup and the constructive statement

Fix one of PR15's carriers with \(J=K+1\) Pythagorean nodes. Write
its integer weights as \(w_i\), so \(\sum_iw_i=q>0\), and put

\[
M_h=\sum_{i=1}^Jw_i(x_i^h+y_i^h),\qquad
T_n=\frac{\binom{2n}{n}}{4^n(2n+1)}M_{2n+1},\qquad
F_N=\sum_{n=0}^NT_n.
\]

Every \(x_i,y_i\) lies in \(\mathbb Z[1/5]\cap(0,1)\), and
\(\sum_{n\ge0}T_n=q\pi/2\). Let \(n_0\) be the explicit
eventual-positivity threshold from PR15. There are fixed positive rational
constants \(C\) and \(\rho<1\) such that, for \(n\ge n_0\),

\[
0<T_n\le C\frac{\rho^n}{2n+1}.
\tag{1}
\]

For the displayed four-node carrier, \(n_0=57\) and
\(\rho=16/25\) are valid. Define the fixed positive integer

\[
L=\operatorname{lcm}(1,3,5,\ldots,4J-1),\qquad
\alpha=Lq\pi/2,\quad \tau_n=LT_n,\quad R_N=LF_N.
\]

**Fixed-multiplier prime-clearing theorem.** For every
\(N\ge n_0-1\) and every positive rational \(\delta\), there
are finitely many indices \(j_p>N\) and positive integers \(z_p\)
such that

\[
G_N=R_N-\sum_p z_p\tau_{j_p}\in\mathbb Z[1/10],
\qquad
0<\sum_pz_p\tau_{j_p}<\delta
\tag{2}
\]

when a correction is needed; the empty sum is allowed otherwise.
There is at most one correction for each prime in the part coprime to ten
of the reduced denominator of \(R_N\). Every correction has

\[
j_p=\frac{h_pp^{e_p}-1}{2},\qquad
1\le h_p\le4J-1,
\qquad
1\le z_p<p^{E_p}\le p^{e_p}\le2j_p+1.
\tag{3}
\]

In particular, the multiplier \(Lq/2\) of \(\pi\) is fixed.
This is an integer signed combination of prefixes of the same carrier:

\[
G_N=R_N+\sum_pz_pR_{j_p-1}-\sum_pz_pR_{j_p}.
\]

Its coefficients sum to one, and their total absolute value, before any
coincident indices are combined, is at most
\(1+2\sum_pz_p\le1+2\sum_p(2j_p+1)\). No additional
Gaussian nodes or variable multiplier of \(\pi\) are introduced.
Taking \(\delta\) to be the original geometric tail majorant gives
\(0<\alpha-G_N\to0\) at the same exponential rate in \(N\)
as the original carrier. The correction indices, and hence the smooth
denominator heights, need not be comparable to \(N\).

## 2. A pole isolated at one nonsmooth prime

Fix a prime \(p\ne2,5\). List the \(2J\) rational legs as
\(u_1,\ldots,u_{2J}\), with the corresponding integer weights
\(b_1,\ldots,b_{2J}\) equal to \(Lw_i\) twice. These legs are
\(p\)-integral. For a unit \(u\), write \(\omega(u)\) for its
Teichmüller representative in \(\mathbb Z_p\); for a nonunit put
\(\omega(u)=0\). Define

\[
C_p(h)=\sum_{r=1}^{2J}b_r\omega(u_r)^h\qquad(h>0).
\]

For every positive \(h\) prime to \(p\) and every \(e\ge0\),

\[
\sum_rb_ru_r^{hp^e}\equiv C_p(h)\pmod{p^{e+1}}.
\tag{4}
\]

For units this follows from
\(u=\omega(u)\langle u\rangle\),
\(\langle u\rangle\in1+p\mathbb Z_p\), and the binomial
valuation of \(\langle u\rangle^{hp^e}-1\). For nonunits,
\(v_p(u^{hp^e})\ge hp^e\ge e+1\). This also supplies an
elementary construction of \(\omega(u)=\lim_{e\to\infty}u^{p^e}\).

Suppose first that \(C_p(h)=0\) for every odd \(h\). Writing
\(2n+1=hp^e\) with \(p\nmid h\), (4) shows that the moment
in \(\tau_n\) has valuation at least \(e+1\). The only possible
denominator factor at \(p\) is \(p^e\), so every \(\tau_n\)
is \(p\)-integral. Thus every \(R_N\) is \(p\)-integral.

Consequently, if \(p\) divides the reduced denominator of \(R_N\),
some odd \(h\) has \(C_p(h)\ne0\). Such an \(h\) can be
chosen at most \(4J-1\). To see this, group the nonzero
Teichmüller values by their squares \(z\). There are at most
\(r\le2J\) distinct squares, and

\[
C_p(2s+1)=\sum_z A_z z^s.
\]

If the first \(r\) such moments vanished, the Vandermonde matrix on
the distinct \(z\)'s would force every \(A_z=0\), and all odd
moments would vanish. Hence a nonzero one occurs with
\(h=2s+1\le2r-1\le4J-1\). If \(p\mid h\), divide out
its powers of \(p\): \(\omega^p=\omega\) preserves the same
moment and leaves a smaller positive odd \(h\).

Fix this \(h\), put \(c=v_p(C_p(h))\ge0\), and take \(e>c\).
Equation (4) gives the exact valuation

\[
v_p\!\left(\sum_rb_ru_r^{hp^e}\right)=c.
\]

At \(j=(hp^e-1)/2\), the bottom \(e\) base-\(p\) digits of
\(j\) are all \((p-1)/2\); doubling them causes no carry. Therefore

\[
v_p\binom{2j}{j}
=v_p\binom{h-1}{(h-1)/2}=:b_h.
\]

It follows that

\[
\boxed{v_p(\tau_j)=c+b_h-e\longrightarrow-\infty.}
\tag{5}
\]

Every other prime outside \(\{2,5,p\}\) in the displayed summand
denominator divides \(h\). The fixed multiplier \(L\), being a
multiple of \(h\), clears it. Thus \(\tau_j\) has no nonsmooth
denominator prime except \(p\). This is an isolated pole, not a
claim that its remaining smooth denominator is small.

## 3. Prime-by-prime correction and its real cost

Let \(p\) have denominator depth \(d>0\) in the current rational
prefix. Choose \(e\) in (5) so that \(E=e-c-b_h\ge d\),
\(j>N\), and \(j\ge n_0\). The number \(p^E\tau_j\) is
a \(p\)-adic unit. There is a unique residue \(z\bmod p^E\)
satisfying

\[
z\equiv(p^E R)\,(p^E\tau_j)^{-1}\pmod{p^E},
\]

where \(R\) is the current prefix. Its representative has
\(1\le z<p^E\), since \(R\) is not \(p\)-integral.
Then \(R-z\tau_j\) is \(p\)-integral. No previously cleared
nonsmooth prime is reintroduced because the correction is integral there.

The added real error has the uniform bound

\[
0<z\tau_j<p^E\tau_j
\le p^eLC\frac{\rho^j}{hp^e}
\le LC\rho^j\longrightarrow0.
\tag{6}
\]

The exponent \(e\) can be increased until this is smaller than any
specified share of \(\delta\). The initial prefix has only finitely
many nonsmooth denominator primes, so these corrections terminate and
prove (2). All choices are finite exact searches; the nonvanishing
argument above proves their termination. No effective bound on the
correction indices in terms of \(N\) alone is asserted.

## 4. Preserving the five-adic denominator can destroy smallness

The preceding construction spends smooth denominator height. A quantitative
obstruction applies to an attempt to avoid that expense by making one
positive late correction sufficiently divisible by five.

Use PR15's ordered Gaussian exponents with largest exponent \(S\),
and write \(v_0=k_0+2\sum_{i=1}^Kk_i\). The source's all-index
summand formula, which has no \(N<5^S\) restriction, gives

\[
d_j:=-v_5(\tau_j)
=2Sj+v_0-2KS-v_5(L)
 -v_5\binom{2j}{j}+v_5(2j+1),\qquad j\ge K.
\tag{7}
\]

Let \(D_N^{(5)}=\max(0,-v_5(R_N))\). For sufficiently large
\(N\), termwise valuation bounds imply

\[
D_N^{(5)}\le2SN+v_0-2KS-v_5(L)
 +\lfloor\log_5(2N+1)\rfloor.
\tag{8}
\]

This upper bound does not assume that the last summand dominates the
prefix. The central-binomial valuation is nonnegative; the largest
possible odd-denominator valuation is the displayed logarithm.

Suppose \(j>N\), \(z\) is a positive integer, and the correction
does not increase the old five-adic denominator:

\[
v_5(R_N-z\tau_j)\ge-D_N^{(5)}.
\tag{9}
\]

If \(d_j>D_N^{(5)}\), the ultrametric inequality forces
\(v_5(z)\ge d_j-D_N^{(5)}\). The same resulting numerical bound
below is trivial if its exponent is nonpositive. A carry count gives
\(v_5\binom{2j}{j}\le\lfloor\log_5(2j)\rfloor+1\), so
(7)--(9) imply

\[
z\ge
\frac{5^{2S(j-N)}}{10j(2N+1)}.
\tag{10}
\]

Let \(y_0\) be the largest real leg and \(\lambda_0>0\) its
normalized weight as in PR15. For \(j\ge n_0\), its positivity
bound and
\(\binom{2j}{j}/4^j\ge1/(2j+1)\) give

\[
\tau_j\ge
\frac{Lq\lambda_0y_0^{2j+1}}{2(2j+1)^2}.
\]

Combining with (10),

\[
\boxed{
z\tau_j\ge
\frac{Lq\lambda_0y_0}{20j(2N+1)(2j+1)^2}
 5^{2S(j-N)}y_0^{2j}.
}
\tag{11}
\]

For the concrete PR15 carrier, \(S=16\) and \(y_0=4/5\).
Uniformly over all integers \(j\ge101N/100\), the right side of
(11) tends to infinity as \(N\to\infty\). Indeed the exponential
base at the smallest allowed relative index has the exact certificate

\[
\left(5^{32/100}(16/25)^{101/100}\right)^{100}
=\frac{2^{404}}{5^{170}}>1.
\tag{12}
\]

The function \((5^{32}16/25)^j/[j(2j+1)^2]\) is increasing for
positive integral \(j\), so the assertion is uniform over all larger
correction indices as well. Polynomial factors in \(N\) cannot
offset this strict exponential margin.

Since \(\alpha-R_N>0\) and the correction is subtracted,
\(\alpha-(R_N-z\tau_j)\ge z\tau_j\). Thus this class of
five-height-preserving corrections eventually makes the unscaled positive
error exceed one. It cannot produce a positive small fully cleared tail.

This statement covers one positive late correction and sequential
implementations that require each step to preserve the original five-adic
height. It does not cover cancellation between several comparable late
indices, corrections of both real signs, or unrestricted coefficients with
a separately proved positive final tail.

## 5. What the construction does and does not supply

Equations (2)--(6) remove PR15's varying nonsmooth multiplier at the cost
of changing the rational approximation by explicitly chosen later source
terms. The fixed number is \(Lq\pi/2\), and the tail stays strictly
positive. The smooth denominator and the integer coefficient heights have
not been suppressed: a correction index \(j\) carries powers of five
of order \(2Sj\), even though \(z\le2j+1\).

Writing \(G_N=A_N/(2^{a_N}5^{b_N})\), a decimal carry certificate
would still require control of

\[
10^{\max(a_N,b_N)}(\alpha-G_N).
\]

The positive approximation estimate in (2) alone gives no small bound
after this multiplication and no control of its fractional part when it
exceeds one. Formula (11) quantifies one failed attempt to repair the
five-adic side; it makes no assertion about the resulting decimal wrap.

The output approximation property is shared by an explicit irrational
word-avoider with the same fixed multiplier. Let
\(\xi=\sum_{n\ge0}t_n10^{-n-1}\), where \(t_n\) is the parity
of the number of ones in the binary expansion of \(n\). This decimal
Thue--Morse number is irrational and avoids digit two. With the same
\(c=Lq/2\), the rationals
\(10^{-m}\lfloor10^mc\xi\rfloor\) lie in
\(\mathbb Z[1/10]\), approach \(c\xi\) from below, and have
error less than \(10^{-m}\). They do not share the actual rational-angle
identity or the prime-isolation proof; they show that fixed-multiplier
smooth approximation with positive error is still insufficient. No new
target-sensitive premise is asserted here.

## 6. Exact reproducibility and finite examples

The accompanying [exact checker](../../../../workflows/experiments/positive_prime_clearing_20261017/audit.py) and [certificate](../../../../workflows/experiments/positive_prime_clearing_20261017/certificate.json) use only Python's standard
library. It reconstructs the four primitive Pythagorean nodes from the
Gaussian exponents \([1,6,11,16]\), computes the rational barycentric
weights, and checks the constants

\[
q=324662081660072025546270114178816356,\qquad L=45045,
\]

so the fixed multiplier \(Lq/2\) is
\(7312201734188972195365868646592391378010\). All mathematical
inputs are in the script; its recorded PR15 commit is provenance, not a
runtime dependency. The finite audit uses exact fractions, modular powers,
and integer inequalities. It needs no decimal digits of \(\pi\),
floating-point arithmetic, downloaded input, or external package.

From the repository root, run:

```sh
python3 workflows/experiments/positive_prime_clearing_20261017/audit.py \
  --json workflows/experiments/positive_prime_clearing_20261017/certificate.json
```

The checked truncation sizes are \(N=80,160,400\). The script
verifies the first three vanishing moments, the positive-tail threshold
\(n_0=57\), each isolated prime valuation, each exact congruence used
to choose \(z_p\), the absence of other rough denominator primes in
each correction, and the resulting smooth denominator. Its selected finite
search is bounded at \(e\le7\); these cases require only
\(e\le3\). The all-index termination statement comes from Sections
2--3, independently of that finite search limit.

In every row the added positive error is less than \(2^{-N}\).
Write the reduced output as \(G_N=A_N/(2^{a_N}5^{b_N})\).

| \(N\) | Rough primes removed | Largest correction index | \(a_N\) | \(b_N\) | Certified upper bound on \(\alpha-G_N\) |
| --- | ---: | ---: | ---: | ---: | ---: |
| 80 | 1 | 793 | 1574 | 25344 | \(10^{31}\) |
| 160 | 4 | 924 | 1834 | 29536 | \(10^{15}\) |
| 400 | 19 | 6384 | 12752 | 204255 | \(10^{-32}\) |

The first two coarse upper bounds are larger than one because the fixed
multiplier and the absolute-weight tail majorant are large; only the third
row certifies a small total error with this majorant. In all three rows
\(A_N\) is prime to ten. Thus the decimal-cleared integer numerator
\(10^{b_N}G_N\) has two-adic valuation \(b_N-a_N\), namely
\(23770,27702,191503\), and five-adic valuation zero. These are
finite observations, not a new all-index numerator law.

For each row the script also proves

\[
10^{b_N}(\alpha-G_N)>1
\]

using the explicit positive lower bound for the first omitted source term.
It separately checks that every listed correction, if multiplied by the
minimum power of five needed to preserve the original prefix's five-adic
denominator height, would itself add error greater than one. These checks
illustrate the arithmetic cost in Section 4 without extrapolating the
finite examples to the all-index statement.
