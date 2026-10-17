# A mixed Salikhov family with simultaneous surviving two- and five-adic precision

Date: 2026-10-17. Labels: `proof sketch` and `experiment`. No Lean verification or novelty claim. This is an arithmetic approximation theorem for the
actual constant pi. It does not supply a prescribed decimal residue, an
error sign, or any digit-occurrence theorem.

## Statement

Use the modified Salikhov coefficients
\(I_j=a_j+b_j\pi\),
\(c_j=2^{2-\lfloor5j/2\rfloor}a_j\), and
\(q_j=2^{2-\lfloor5j/2\rfloor}b_j>0\).
For every \(k\ge1\), the construction below gives an explicit positive
integer \(q_k^*\), a rational \(c_k^*\), and a reduced fraction

\[
-c_k^*/q_k^*=P_k^*/Q_k^*,\qquad Q_k^*>0,
\]

such that

\[
v_5(Q_k^*)=k,\qquad Q_k^*\text{ is odd},\qquad v_2(q_k^*)\le9.
\tag{1}
\]

The reduced numerator retains a linearly growing power of two. More
precisely, put \(n_k=(5^k+1)/2\), and let \(r_k\) be the second
index constructed below. For all \(k\ge7\),

\[
\frac{31}{32}n_k<r_k\le n_k,\qquad
v_2(P_k^*)\ge2r_k-\lfloor\log_2(4r_k+1)\rfloor-8.
\tag{2}
\]

The approximation rate is stronger than mere convergence: for all
sufficiently large \(k\),

\[
\boxed{0<\left|\pi-\frac{P_k^*}{Q_k^*}\right|
\le (Q_k^*)^{-21/20}.}
\tag{3}
\]

The denominators tend to infinity by their exact five-adic orders.
No statement is made that these are continued-fraction convergents.

## Inputs already established separately

The source is [Zeilberger--Zudilin, arXiv:1912.06345v2, Part II](https://arxiv.org/html/1912.06345v2),
together with PI's [local-pair proof sketch](20260906-salikhov-mod5-support.md)
and the new [companion-survival proof sketch](20261017-salikhov-companion-survival.md).
Their exact normalizations are used throughout. The local-pair note also
proves \(b_j>0\) at every positive index by induction from the recurrence:
the polynomial \(-10000P_2-P_1-10^8P_3\) has positive coefficients,
and \(b_2>10000b_1>0\). Thus the positivity used in the mixtures is an
all-index input, not an eventual sign inferred from asymptotics.

1. At \(n_k=(5^k+1)/2\),
   \(v_5(q_{n_k})=k\) and \(v_5(c_{n_k})=0\).
2. Every \(j\ge1\) satisfies
   \[
   v_2(c_j)\ge H_j:=2j+1-\lfloor\log_2(4j+1)\rfloor,
   \qquad v_5(c_j)\ge-\lfloor\log_5(4j)\rfloor.
   \]
3. If \(r=2^L m\), \(L\ge2\), \(m\) odd, and
   \(s_2(3m)\le L\), then \(v_2(q_r)=s_2(3m)\).
4. If \(\Lambda\) is the large positive root and \(\rho\) the
   modulus of either small conjugate root of
   \[
   108X^3-2359989X^2+138304X-2048,
   \]
   the actual coefficient sequences satisfy
   \[
   \log q_j=(\log\Lambda-\tfrac52\log2)j+o(j),\qquad
   |\pi+c_j/q_j|\le\exp[-\log(\Lambda/\rho)j+o(j)].
   \]

These are explicit hypotheses on known source sequences, not properties
silently inferred from a numerical pi prefix. The analytic input is the
published recurrence/asymptotic argument for the actual integral.

## 1. A nearby index with a bounded multiplier valuation

For \(n=n_k\ge2^{14}\), set

\[
L=\lfloor\log_2n\rfloor-6,\qquad
m=\max\{u\le n/2^L:u\text{ is a positive odd integer}\},\qquad
r=2^Lm.
\]

Then \(L\ge8\), \(63\le m<128\), and
\(0\le n-r<2^{L+1}\le n/32\). Since \(3m<384<2^9-1\),
its binary digit sum is at most eight. The even-index congruence therefore
gives the exact and uniformly bounded value

\[
e:=v_2(q_r)=s_2(3m)\le8.
\tag{4}
\]

For the finitely many \(k\le6\), take \(r\) to be the least power
of two at least \(n_k\). Then \(r\ge4\), and the same even-index
theorem gives \(e=2\). These finite choices are used for (1), while
the eventual approximation statement uses only the first construction.

## 2. Two choices suffice to preserve both primes

Set

\[
s=\lfloor\log_5(4r)\rfloor,\qquad T=5^{k+s+1}.
\]

For \(\lambda\in\{1,3\}\), define

\[
q^{(\lambda)}=q_n+\lambda Tq_r,\qquad
c^{(\lambda)}=c_n+\lambda Tc_r.
\]

Both \(q^{(\lambda)}\) are positive integers. Their difference is
\(2Tq_r\), whose two-adic order is exactly \(e+1\). Therefore
they cannot both be divisible by \(2^{e+2}\). Choose \(\lambda=1\)
if \(q^{(1)}\not\equiv0\pmod{2^{e+2}}\); otherwise choose
\(\lambda=3\). This gives a literal finite modular algorithm and

\[
v_2(q_k^*)=v_2(q^{(\lambda)})\le e+1\le9.
\tag{5}
\]

At five,

\[
v_5(\lambda Tq_r)\ge k+s+1>k,
\qquad
v_5(\lambda Tc_r)\ge k+1>0.
\]

Since \(v_5(q_n)=k\) and \(v_5(c_n)=0\), no cancellation is
possible in either leading unit:

\[
v_5(q_k^*)=k,\qquad v_5(c_k^*)=0.
\tag{6}
\]

At two, \(\lambda T\) is odd, so
\(v_2(c_k^*)\ge\min(H_n,H_r)\). The exact reduced-fraction
valuation identities give

\[
v_5(Q_k^*)=k,\qquad
v_2(P_k^*)\ge\min(H_n,H_r)-e-1.
\tag{7}
\]

The latter bound is positive. For \(k\le6\), the minimum is
\(H_n\ge H_3=4\) and \(e=2\); for \(k\ge7\), both indices
are large and \(e\le8\). Thus \(Q_k^*\) is odd in every case.
The function \(H_j\) is increasing for positive integers, so for
\(k\ge7\), (7) gives exactly (2).

## 3. A common denominator bound and the approximation rate

The rational denominator of \(c_j\) divides the odd part of
\(\operatorname{lcm}(1,\ldots,4j)\). This follows directly from
the endpoint formula in the local-pair note: all endpoint and coefficient
numerators lie in \(\mathbb Z[1/2]\), and every odd integration
denominator is at most \(4j-1\). The proved two-adic integrality of
\(c_j\) removes any remaining power of two from its denominator.

For \(k\ge7\), both rational companions are therefore cleared by

\[
D_n=\operatorname{oddpart}(\operatorname{lcm}(1,\ldots,4n)).
\]

The prime number theorem gives \(\log D_n\le4n+o(n)\).
Also
\(\lambda T\le15\cdot5^k\cdot4r<120nr\), so the mixing
coefficient is at most polynomial in \(n\). Put

\[
B=\log\Lambda-\tfrac52\log2,\quad A=B+4,\quad
\gamma=\log(\Lambda/\rho).
\]

The reduced denominator satisfies

\[
Q_k^*\le D_nq_k^*\le\exp[An+o(n)].
\tag{8}
\]

Because both mixing weights are positive, the mixed rational number is
the convex combination

\[
-\frac{c_k^*}{q_k^*}
=\frac{q_n}{q_n+\lambda Tq_r}\left(-\frac{c_n}{q_n}\right)
 +\frac{\lambda Tq_r}{q_n+\lambda Tq_r}\left(-\frac{c_r}{q_r}\right).
\]

Its absolute error is at most the larger of the two source errors. Thus

\[
\left|\pi-\frac{P_k^*}{Q_k^*}\right|
\le\exp[-\gamma r+o(n)]
\le\exp[-\tfrac{31}{32}\gamma n+o(n)].
\tag{9}
\]

The strict inequality

\[
\frac{31}{32}\gamma>\frac{21}{20}A
\tag{10}
\]

has an elementary exact certificate. The cubic changes sign between
21000 and 22000, so \(\Lambda>21000\), and its root product gives
\(\rho^2=2048/(108\Lambda)\). Substituting this relation into
(10) and multiplying by 320 reduces it to

\[
\Lambda^{129}3^{465}>2^{555}e^{1344}.
\]

The bound \(e<11/4\), together with the exact integer comparison

\[
21000^{129}3^{465}4^{1344}>2^{555}11^{1344},
\]

proves the claim. The strict margin in (10) absorbs the \(o(n)\)
terms in (8)--(9), proving (3). Irrationality of pi makes the error
nonzero.

## Scope

This construction removes the simultaneous-prime cancellation obstacle
for a new family of positive mixtures. It does not prove a bound for the
individual \(v_2(q_{N_k})\). It supplies no target interval for
\((10^sP_k^*\bmod Q_k^*)/Q_k^*\), no favorable error sign, and no
control of the other denominator primes. Those missing ordered residues
remain the decimal-occurrence obstruction.

### What the positive coefficient can certify

Write \(R_j=-c_j/q_j\) and allow any positive \(\lambda\). Exactly,
\[
R(\lambda)-R_n
=\frac{\lambda Tq_r}{q_n+\lambda Tq_r}(R_r-R_n).
\]
Thus all such mixtures lie between the two source approximants. At the
explicit unbounded decimal horizon \(s_k=5n_k\), the same convex bound
and the exact inequality
\[
\frac{31}{32}\gamma>5\log10
\]
show that, for some \(\eta>0\), eventually and uniformly in all positive
\(\lambda\),
\[
|10^{5n_k}(R(\lambda)-\pi)|\le e^{-\eta n_k}.
\]
The inequality follows from the root product as above and the exact integer
comparison \(21000^{93}3^{93}>2^{599}5^{320}\), which the checker verifies.
For any fixed word length, all mixture phases eventually lie in at most
two adjacent decimal cells, including wraparound. Varying the coefficient
cannot sweep all prescribed target cells at that horizon. This makes no
claim that the actual center phases fail to visit a given cell as k varies;
that recurrence is still unproved.

There is also a bound on what the inherited absolute-error intervals can
certify at any horizon. If \(\pi\in I_n\cap I_r\), where
\(I_j=[R_j-\delta_j,R_j+\delta_j]\), put
\(w=\lambda Tq_r/(q_n+\lambda Tq_r)\). The mixture interval is
\(I_\lambda=(1-w)I_n+wI_r\), and exactly
\[
I_n\cap I_r\subseteq I_\lambda.
\]
Indeed, a point belonging to both intervals belongs to their convex weighted
sum. Any robust cylinder containment derived from \(I_\lambda\) was
already implied by the intersection of the two original certificates.
Additional signed or target-specific information is required to obtain a
new target certificate from this choice of coefficient.

## An explicit irrational word-avoider with stronger abstract approximation data

The abstract properties above still do not separate pi from word-avoiders,
even after retaining a denominator-relative approximation rate greater
than one. This can be shown constructively.

Let \(t_0=0\), \(t_{2j}=t_j\), \(t_{2j+1}=1-t_j\), and put
\(\xi=\sum_{j\ge0}t_j10^{-j}\). This number uses only decimal digits
0 and 1, so it avoids the digit 2. Bugeaud's theorem in
[On the rational approximation to the Thue--Morse--Mahler numbers](https://aif.centre-mersenne.org/articles/10.5802/aif.2666/)
gives \(\mu(\xi)=2\).

For each \(k\ge1\), choose consecutive convergents
\(p_j/q_j\), \(p_{j-1}/q_{j-1}\) so late that

\[
q_j\ge\max(5^{20(k+1)},2^{40}),\qquad
q_{j-1}\ge q_j^{9/10}.
\]

Such choices exist. Indeed, the exponent-two lower bound with exponent
\(2+1/9\), combined with the convergent upper bound
\(|\xi-p_{j-1}/q_{j-1}|<1/(q_{j-1}q_j)\), gives the second
inequality eventually. Define

\[
H=\lfloor\tfrac12\log_2q_j\rfloor,\qquad M=2^H5^{k+1}.
\]

The convergent matrix
\(\begin{pmatrix}p_j&p_{j-1}\\q_j&q_{j-1}\end{pmatrix}\)
has determinant \(\pm1\). It is therefore invertible modulo \(M\).
Choose \(a,b\in\{1,\ldots,M\}\) such that

\[
P=ap_j+bp_{j-1}\equiv0\pmod{2^H},\qquad
P\equiv1\pmod{5^{k+1}},
\]
\[
Q=aq_j+bq_{j-1}\equiv1\pmod{2^H},\qquad
Q\equiv5^k\pmod{5^{k+1}}.
\]

The Chinese remainder theorem first specifies the target vector
\((P,Q)\) modulo \(M\), and matrix inversion supplies \((a,b)\).
Selecting the positive representative of each residue gives the stated
coefficient bounds.

After reducing \(P/Q\) to \(\widehat P/\widehat Q\), any canceled
factor is prime to 10. Hence

\[
\widehat Q\text{ is odd},\qquad
v_5(\widehat Q)=k,\qquad v_2(\widehat P)\ge H.
\]

Since \(a,b\) are positive, the same convex-combination argument gives

\[
\left|\xi-\frac{\widehat P}{\widehat Q}\right|
\le\frac1{q_{j-1}q_j}\le q_j^{-19/10}.
\]

Moreover
\(\widehat Q\le Q\le2Mq_j\le2q_j^{31/20}\). The chosen
threshold \(q_j\ge2^{40}\) implies

\[
\boxed{
0<\left|\xi-\frac{\widehat P}{\widehat Q}\right|
\le\widehat Q^{-6/5},\qquad
v_2(\widehat P)\ge\tfrac14\log_2\widehat Q.
}
\]

For the error bound, \(q_j^{1/25}\ge2^{6/5}\) suffices. For the
valuation bound, combine
\(H\ge\tfrac12\log_2q_j-1\) with
\(\log_2\widehat Q\le1+\tfrac{31}{20}\log_2q_j\).

This gives an explicit irrational word-avoider with exact unbounded
five-adic denominator depth, odd reduced denominators, a positive
proportion of two-adic numerator digits, and an approximation exponent
\(6/5>21/20\). It does not reproduce the Salikhov recurrence or exact
integral. Those exact identities alone still have to yield the missing
ordered decimal residue before this arithmetic can become a V1 premise.

One may also prescribe any numerator-depth function of \(k\): impose
the additional threshold \(q_j\ge2^{2F(k)}\) to get
\(v_2(\widehat P)\ge F(k)\). In particular, \(F(k)=2n_k\)
dominates the linear-in-\(n_k\) lower bound in (2). Arbitrarily late
convergents allow this extra threshold, and none of the preceding bounds
is weakened. This observation does not identify the source's exact
absolute error rate as a function of \(n_k\), or its recurrence.

## Reproducible finite checks

Label: `experiment`. The finite checks support the formulas and
normalizations; the all-index conclusions require the arguments above.
Both scripts use the Python standard library, exact integers and rational
numbers, and no floating-point pi approximation or network access.

Suggested repository commands are:

```sh
python3 workflows/experiments/salikhov_mixed_precision_20261017/mixed_branch.py --json workflows/experiments/salikhov_mixed_precision_20261017/certificate.json
python3 workflows/experiments/salikhov_mixed_precision_20261017/thue_morse_precision_separator.py --json workflows/experiments/salikhov_mixed_precision_20261017/separator_certificate.json
```

The first script reproduces the published recurrence independently of
the modular evaluator. Its default run checks five complete reduced
fractions, all ten selected source-companion denominators against the
odd least common multiple, 100 modular mixture choices, and the exact
integer inequality proving the constant margin in (10). The first five
reduced pairs have:

| \(k\) | \(n_k\) | \(r_k\) | \(\lambda\) | \(v_5(Q_k^*)\) | \(v_2(P_k^*)\) | proved lower bound |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 4 | 1 | 1 | 4 | 1 |
| 2 | 13 | 16 | 1 | 2 | 23 | 19 |
| 3 | 63 | 64 | 3 | 3 | 119 | 117 |
| 4 | 313 | 512 | 1 | 4 | 621 | 614 |
| 5 | 1563 | 2048 | 1 | 5 | 3120 | 3112 |

The modular calculation uses the actual \(q_n\) residues, not residues
divided by different odd units at the two indices. Among its first 100
mixtures the largest multiplier valuation is eight; the proof allows
nine. Only \(k=3\) requires the coefficient three in this sample.

The separator script encloses the infinite Thue--Morse number in an exact
rational interval from its first 512 digits, certifies 516 common
continued-fraction digits, and constructs eight reduced pairs. It checks
the exact prime valuations, the quarter-logarithm numerator bound, and
the error inequality \(E^5\widehat Q^6\le1\), where \(E\) is a
certified upper bound for the distance from the rational pair to every
point of that interval. It does not substitute the finite decimal prefix
for the infinite number. The optional larger numerator-depth threshold
above is an all-index consequence and is not part of this default finite
sample.


The modular evaluator uses the all-index truncation formula in the
[odd-multiplier note](20261017-salikhov-odd-multiplier.md), from PR #14.
The present proof and quantitative separator were independently reviewed
by two readers, including the full denominator-clearing step and the
strict asymptotic margin. A third review checked the target-sensitivity
and interval-containment identities. Labels remain proof sketch and
experiment; no claim is promoted by the finite samples or by repository CI.
