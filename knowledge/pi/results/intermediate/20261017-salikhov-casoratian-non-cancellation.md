# A third Salikhov contour and a determinant that forces surviving five-adic depth

Date: 2026-10-17. Labels: *proof sketch* and *experiment*. The exact
algebraic certificate is reproducible; no Lean verification or novelty
claim is made. This is a theorem about rational approximants to the
actual constant pi. It does not prove a decimal occurrence.

## Statement

Use the modified Salikhov coefficients and reduced approximants
\[
 I_n=a_n+b_n\pi,\qquad
 R_n=-a_n/b_n=P_n/Q_n,\qquad Q_n>0.
\]
The [local-pair note](20260906-salikhov-mod5-support.md) proves \(b_n>0\)
and fixes these normalizations.

For \(L\ge3\), define an index set with a fixed low base-five prefix:
\[
 \mathcal D_L=
 \left\{36+\sum_{j=3}^{L-1}d_j5^j:d_j\in\{1,2\}\right\}.
 \tag{1}
\]
The prefix is \(121_5=36\); these are restrictions on an auxiliary
integer index, not on the digits of pi. For \(n\in\mathcal D_L\), let
\(T(n)\) be the number of free digits equal to two.

**Individual survival in every triple.** For every \(n\in\mathcal D_L\),
\[
 \boxed{\min_{0\le r\le2}v_5(a_{n+r})\le2-T(n).}
 \tag{2}
\]
Consequently there is an index \(j(n)\in\{0,1,2\}\) such that
\[
 v_5(Q_{n+j(n)})\ge \max\{0,T(n)-2\}.
 \tag{3}
\]
Choose \(j(n)\) to be the least index attaining the minimum in (2).
This is a finite exact rule using rational coefficients alone.

**Many indices of both actual error signs.** Retain only bases with
\(T(n)\ge (L-3)/3\). For each sign \(\sigma\in\{-1,1\}\), and every
sufficiently large \(L\),
\[
 \#\left\{n\in\mathcal D_L:
 T(n)\ge (L-3)/3,\quad
 \sigma\bigl(\pi-R_{n+j(n)}\bigr)>0\right\}
 \ge \frac25\,2^{L-3}.
 \tag{4}
\]
Every retained selected index has
\[
 v_5(Q_{n+j(n)})\ge (L-9)/3.
 \tag{5}
\]
The triples in this construction are disjoint.

In particular, put \(\delta=\log_5 2\). Before every sufficiently large
cutoff \(X\), each actual error sign occurs at
\(\gg X^\delta\) selected indices whose denominators satisfy
\[
 v_5(Q_j)\ge \frac13\log_5 X-4.
 \tag{6}
\]
The power \(\delta=0.430676\ldots\) counts indices, as in the existing
Salikhov family statements. The proof does not assert a two-adic
numerator bound on this new index set.

The determinant mechanism is stronger than a shared multiplier
divisibility statement: (2) forces a negative valuation of the rational
companion itself when \(T(n)>2\). It therefore proves survival after
reduction without assuming that a multiplier and companion do not
cancel.

## 1. The missing third solution is an actual contour

The primary source is
[Zeilberger--Zudilin, arXiv:1912.06345v2, Part II, equations (1)--(3)](https://arxiv.org/html/1912.06345v2).
Write
\[
 V(y)=y^2+6y+25,\qquad
 {\cal R}_n(x)=\frac{5x^{2n}V(x^2)^{2n}}{(25-x^2)^{3n+1}},
 \qquad \beta=-1+2i.
\]
In its symmetric partial fractions,
\[
 {\cal R}_n(x)=P_n^{\rm pol}(x)+
 \sum_{j=0}^{3n}A_{n,j}
 \big((5-x)^{-j-1}+(5+x)^{-j-1}\big),
 \tag{7}
\]
choose the rational primitive
\[
 F_n(x)=\int_0^xP_n^{\rm pol}(t)\,dt+
 \sum_{j=1}^{3n}\frac{A_{n,j}}j
 \big((5-x)^{-j}-(5+x)^{-j}\big).
 \tag{8}
\]
It is odd and has rational coefficients. The remaining primitive term
is \(A_{n,0}\log((5+x)/(5-x))\). As in the source normalization,
\[
 a_n=2(-1)^n\operatorname{Im}F_n(\beta),\qquad
 b_n=(-1)^nA_{n,0}/2.
 \tag{9}
\]
Define the rational sequence
\[
 d_n=2(-1)^n\operatorname{Re}F_n(\beta).
 \tag{10}
\]

The horizontal contour joining \(\beta\) to \(1+2i=-\bar\beta\) gives
\[
 J_n=(-1)^{n+1}\int_{\beta}^{-\bar\beta}{\cal R}_n(x)\,dx
     =d_n-2b_n\log2.
 \tag{11}
\]
Indeed, the rational primitive difference is
\(-2\operatorname{Re}F_n(\beta)\). The logarithmic ratios at the
vertical endpoints are \((1+i)/2\) and \((1-i)/2\); their product is
\(1/2\). Continuing the logarithm along the horizontal segment gives
the difference \(\log2\). All these segments avoid the poles at
\(\pm5\), and the endpoint logarithms may equivalently be fixed
continuously in the upper half-plane.

### Exact homogeneous recurrence, including its boundary

Let \(p_0(n),\ldots,p_3(n)\) be the four polynomials in the
[published recurrence](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt).
Set \(f_n(x)=(-1)^n{\cal R}_n(x)\), \(y=x^2\), and \(T(y)=25-y\).
The audit constructs a polynomial \(S(n,y)\in\mathbb Q[n,y]\), of
degree eight in \(n\) and twelve in \(y\), and checks the following
identity as an equality of formal bivariate polynomials:
\[
\begin{split}
 2yV(y)T(y)\,\partial_yS+
 \big((2n+1)(V(y)+2yV'(y))T(y)+(6n+18)yV(y)\big)S\\
 =\sum_{\ell=0}^3p_\ell(n)(-yV(y)^2)^\ell T(y)^{9-3\ell}.
\end{split}
 \tag{12}
\]
The complete rational coefficient array is recorded in the
certificate. It is reconstructed by interpolation and then checked
by direct polynomial multiplication; its validity is not inferred
from sampled recurrence values.

Taking the logarithmic derivative of \(f_n\), (12) is exactly
\[
 \sum_{\ell=0}^3p_\ell(n)f_{n+\ell}(x)
 =
 \frac{d}{dx}
 \left(f_n(x)\,
       \frac{xV(x^2)S(n,x^2)}{(25-x^2)^8}\right).
 \tag{13}
\]
The right-hand primitive vanishes at each of the four roots
\(\pm1\pm2i\) of \(V(x^2)\). Its zero has order at least \(2n+1\);
the denominator is nonzero there. In particular this holds at
\(n=0\), so no initial boundary term has been discarded.

Integration proves the same homogeneous recurrence for \(I_n\) and
\(J_n\). The source logarithmic coefficient \(b_n\) also satisfies it,
either by residues in (13) or by the source recurrence. Equation (11)
then proves it for \(d_n\).

The exact initial values are
\[
\begin{array}{c|ccc}
 n&0&1&2\\ \hline
 a_n&0&-11272/3&-6156093056/105\\
 b_n&1/4&1196&18662336\\
 d_n&0&1658&2716506572/105 .
\end{array}
 \tag{14}
\]
They will certify independence, rather than leaving it as an
assumption about a formal third solution.

## 2. A proved denominator budget for the third solution

The exact local coefficients satisfy
\[
 C_{n,j}:=5^{-j}A_{n,j}
 =[w^{3n-j}]
 \frac{(w-1)^{2n}(25(w-1)^4+6(w-1)^2+1)^{2n}}
 {(2-w)^{3n+1}}
 \in\mathbb Z[1/2].
 \tag{15}
\]
At \(x=\beta\),
\[
 \frac5{5-\beta}=\frac{3+i}{4},\qquad
 \frac5{5+\beta}=\frac{2-i}{2}.
\]
Thus every partial-fraction term of \(F_n(\beta)\) is a Gaussian
number in \(\mathbb Z[1/2,i]\) divided by an integer
\(1\le j\le3n\).

The polynomial part has integer coefficients and degree \(4n-2\).
Its primitive at the Gaussian integer \(\beta\) has integration
denominators at most \(4n-1\). Taking real and imaginary parts
introduces no odd denominators. Therefore, for \(n\ge1\),
\[
 v_5(a_n)\ge-\lfloor\log_5(4n)\rfloor,\qquad
 \boxed{v_5(d_n)\ge-\lfloor\log_5(4n)\rfloor.}
 \tag{16}
\]
Also \(v_5(b_n)\ge0\), since the source normalized multiplier
\(q_n=2^{2-\lfloor5n/2\rfloor}b_n\) is integral.

These are bounds for the actual third contour solution. There is
no premise that an arbitrary rational fundamental solution has
logarithmic denominator loss.

## 3. The full Casoratian and its factorial formula

Use rows at three consecutive indices and columns in the order
\((a,b,d)\):
\[
 W_n=\det
 \begin{pmatrix}
 a_n&b_n&d_n\\
 a_{n+1}&b_{n+1}&d_{n+1}\\
 a_{n+2}&b_{n+2}&d_{n+2}
 \end{pmatrix}.
\]
From (14), \(W_0=2760952/63\ne0\). The recurrence gives
\[
 \frac{W_{n+1}}{W_n}=-\frac{p_0(n)}{p_3(n)}
 =
 \frac{1024(2n+5)(2n+3)(2n+1)(n+2)(n+1)g(n+1)}
 {3(4n+11)(3n+8)(3n+7)(4n+9)(n+3)g(n)},
 \tag{17}
\]
where
\[
 g(n)=559455n^4+3399916n^3+7651391n^2+7554302n+2760952.
\]
Every factor in (17) is nonzero for \(n\ge0\).

Telescoping gives the exact formula
\[
 \boxed{
 W_n=\frac{800}{3}\,512^n g(n)\,
 \frac{(2n)!(2n+2)!((2n+4)!)^2(n+1)!}
      {((n+2)!)^2(4n+8)!(3n+5)!}.}
 \tag{18}
\]
One may verify it directly: the value at zero is \(g(0)/63\);
the quotient at \(n+1\) and \(n\) cancels to (17).

For an odd prime \(p=5\), Legendre's formula now gives
\[
 v_5(W_n)=2+v_5(g(n))+\sum_{\ell\ge1}E_{5^\ell}(n),
 \tag{19}
\]
where
\[
\begin{split}
 E_M(n)={}&
 \left\lfloor\frac{2n}{M}\right\rfloor+
 \left\lfloor\frac{2n+2}{M}\right\rfloor+
 2\left\lfloor\frac{2n+4}{M}\right\rfloor+
 \left\lfloor\frac{n+1}{M}\right\rfloor\\
 &-2\left\lfloor\frac{n+2}{M}\right\rfloor-
 \left\lfloor\frac{4n+8}{M}\right\rfloor-
 \left\lfloor\frac{3n+5}{M}\right\rfloor .
\end{split}
 \tag{20}
\]
The sum is finite. Also \(E_M(n+M)=E_M(n)\), because the
coefficients of the added integer parts sum to zero.

## 4. A digit restriction on indices makes the budget favorable

For \(n\in\mathcal D_L\), every prefix modulo \(5^\ell\), for
\(3\le\ell\le L\), lies in \(\mathcal D_\ell\). Its exact range is
\[
 \frac{5^\ell+19}{4}
 \le n\bmod5^\ell
 \le\frac{5^\ell-53}{2}.
 \tag{21}
\]
The lower and upper endpoints come from taking every free digit
equal to one and every free digit equal to two, respectively.

Since \(n\equiv36\equiv1\pmod5\),
\(g(n)\equiv(n+1)(n^2+2)\equiv1\pmod5\). Thus \(v_5(g(n))=0\).
For the first three levels, direct integer floors give
\[
 E_5(n)=E_{25}(n)=E_{125}(n)=-1.
 \tag{22}
\]
For \(4\le\ell\le L\), put \(M=5^\ell\) and let \(d=d_{\ell-1}\)
be the new highest digit of that prefix. If \(d=1\), the prefix
is between \(M/4+19/4\) and \(3M/10-53/2\). Formula (20) has
only one nonzero term, namely
\(-\lfloor(4n+8)/M\rfloor=-1\).
If \(d=2\), the prefix is between \(9M/20+19/4\) and
\(M/2-53/2\). The additional term
\(-\lfloor(3n+5)/M\rfloor=-1\) is the only change. Consequently
\[
 E_{5^\ell}(n)=-d_{\ell-1}\qquad(4\le\ell\le L).
 \tag{23}
\]
For \(\ell>L\), all floors vanish by the upper bound in (21).
Combining (19), (22), and (23) gives
\[
 \boxed{v_5(W_n)=2-L-T(n).}
 \tag{24}
\]

The same range proves, for each \(r=0,1,2\),
\[
 5^L\le4(n+r)<5^{L+1}.
 \tag{25}
\]
Thus every \(d_{n+r}\) has valuation at least \(-L\) by (16).
Every \(b_{n+r}\) has nonnegative valuation. Expanding \(W_n\)
along its \(a\)-column therefore yields
\[
 v_5(W_n)\ge \min_{0\le r\le2}v_5(a_{n+r})-L.
 \tag{26}
\]
Equations (24) and (26) prove (2).

For any rational \(a\) and nonzero rational \(b\), reduction of
\(-a/b=P/Q\), \(Q>0\), gives
\[
 v_5(Q)=\max\{0,v_5(b)-v_5(a)\}.
 \tag{27}
\]
Since \(v_5(b_{n+r})\ge0\), (3) follows without any extra
noncancellation assertion.

## 5. Both signs and the count before every cutoff

The actual signed asymptotic from the
[local-pair note](20260906-salikhov-mod5-support.md#signed-asymptotic-for-the-actual-integral)
is
\[
 \pi-R_j=K_0(\rho/\Lambda)^j
 \big(\cos(j\theta+\varphi)+O(1/j)\big),\qquad K_0>0.
 \tag{28}
\]
Here \(\alpha,\bar\alpha\) are the nonreal roots of
\[
 108X^3-2359989X^2+138304X-2048,
 \qquad \theta=\arg\alpha\in(0,\pi/2).
\]
The source's irrational-phase argument proves
\(\theta/\pi\notin\mathbb Q\). Its exact ingredients are
irreducibility modulo eleven and discriminant
\(-57(4475640000)^2\). The splitting field is an \(S_3\)-extension
with unique quadratic subfield \(\mathbb Q(\sqrt{-57})\), so its
only roots of unity are \(1\) and \(-1\).
The ratio \(\alpha/\bar\alpha\) is neither: the roots are nonreal
and \(\operatorname{Re}\alpha>0\).

Here is a self-contained exact enclosure for this phase. Put
\(A=87407/4\), \(C=512/27\), and
\[
 \ell=\frac{218516913962}{10^7},\qquad
 u=\frac{218516913963}{10^7}.
\]
Writing \(\chi\) for the cubic above, direct integer arithmetic gives
\(\chi(\ell)<0<\chi(u)\). The negative discriminant proves that
its unique real root \(\Lambda\) lies in \((\ell,u)\), and
\(0<A-u<A-\ell\). Vieta's formulas give
\[
 |\alpha|^2=C/\Lambda,\qquad
 \operatorname{Re}\alpha=(A-\Lambda)/2>0.
\]
The following rational comparisons are checked literally in the audit:
\[
 \frac{162}{41}
 <\frac{\ell(A-u)^2}{C}
 \le\frac{\Lambda(A-\Lambda)^2}{C}
 \le\frac{u(A-\ell)^2}{C}
 <\frac{384}{97}.
\]
Consequently
\[
 \frac1{96}<\tan^2\theta
 =\frac{4C}{\Lambda(A-\Lambda)^2}-1<\frac1{81}.
\]
Since \(0<\theta<\tan\theta\) and \(\pi>3\), this proves
\[
 0<\theta<1/9,\qquad \theta/\pi<1/27.
 \tag{29}
\]

For each nonzero integer \(m\), the normalized Fourier sum on
\(\mathcal D_L\) has absolute value
\[
 \left|2^{-(L-3)}
       \sum_{n\in\mathcal D_L}e^{imn\theta}\right|
 =
 \prod_{j=3}^{L-1}\left|\cos\!\left(\frac{m5^j\theta}{2}\right)\right|
 \longrightarrow0.
 \tag{30}
\]
Here is the complete convergence argument. If the product had a
positive limit, the squared sines of its arguments would have a
finite sum, so
\(\operatorname{dist}(5^j m\theta/(2\pi),\mathbb Z)\to0\).
For nearest integers \(u_j\), sufficiently small errors imply
\(u_{j+1}=5u_j\); the errors then multiply by five while tending
to zero. They must eventually vanish, contradicting the
irrationality of \(\theta/\pi\). Weyl's criterion proves relative
equidistribution of \(n\theta+\varphi\) on these finite index sets.
This uses neither a claim about the decimal orbit of pi nor a
growth estimate for a varying-modulus exponential sum.

Let \(\varepsilon=\pi/20\). The starting-phase interval
\[
 [-\pi/2+\varepsilon,\ \pi/2-2\theta-\varepsilon]
 \tag{31}
\]
has relative length \(9/20-\theta/\pi>223/540>2/5\).
For a starting phase in this interval, all three cosines at
indices \(n,n+1,n+2\) are at least \(\sin\varepsilon>0\).
Its translate by \(\pi\) gives the negative margin. For all
sufficiently large indices the remainder in (28) is smaller
than half this margin. The rule selecting \(j(n)\) therefore
has no effect on the sign for these bases.

Among the \(2^h\) words of length \(h=L-3\), the number having
fewer than \(h/3\) digits equal to two is at most
\[
 \left(\frac{3}{2^{2/3}}\right)^h=o(2^h).
 \tag{32}
\]
This follows by weighting the binomial sum with \(z=1/2\);
the strict inequality \(3/2^{2/3}<2\) is equivalent to \(27<32\).
Deleting these words does not change either limiting phase
proportion. The strict margin above \(2/5\) proves (4), and (3)
proves (5).

Within one \(\mathcal D_L\), different bases differ by at least
\(125\), so their triples do not intersect. The ranges (21) also
separate successive values of \(L\). Finally take the largest
\(L\) with \((5^L-49)/2\le X\). Its entire block of triples lies
before \(X\), and \(5^L>(2X+49)/5\). Thus
\(2^{L-3}\gg X^{\log_5 2}\) and \(L>\log_5X-1\), proving (6)
and the stated count for each sign.

The algebraic inequalities and index sets are explicit. The phrase
“sufficiently large” in the sign count inherits the source asymptotic
and the qualitative convergence in (30); this note gives no numerical
cutoff or effective discrepancy rate.

## Scope and exact verification

The new ingredient is the third contour with its certified boundary,
followed by an exact determinant valuation that forces a reduced
denominator contribution. This does not rely on the one-sided
common-divisibility data from the
[full-pair growing-precision note](20261017-salikhov-full-pair-growing-precision.md).
The individual selected indices here need not belong to its binary
family, and the two-adic numerator conclusion from that family is
not transferred to them.

The error signs are signs of approximation to the actual pi.
Replacing pi by \(4/9\), while keeping these source rational
approximants, makes all sufficiently late errors negative since
\(R_n\to\pi\). The two-sign conclusion thus uses a real source
connection constant. It still supplies no ordered value of
\((10^sP_n\bmod Q_n)/Q_n\), which is the missing decimal information.

The accompanying audit uses exact integer and rational arithmetic,
no pi digit expansion, and no network access. It reconstructs and
checks (12) formally; checks the endpoint formula, initial
determinant and recurrence; and checks the floor identities and
forced valuations on finite words and exact coefficient samples.
Finite samples are kept separate from the all-index arguments above.

The intended repository command is:

    python3 workflows/experiments/salikhov_casoratian_20261017/audit.py --json workflows/experiments/salikhov_casoratian_20261017/certificate.json

From an external staging directory, pass the PI checkout with
the optional argument \(\texttt{--repo-root}\).

The recorded default run verifies the formal bivariate telescoper
and formal polynomial Casoratian quotient; direct endpoint formulas
and all consecutive determinants through index sixteen; all 2,047
index words with at most ten free digits; and fifteen actual triples
through index 7,788. The large coefficient computation reserves every
possible valuation lost at a recurrence division, beginning with
11,695 base-five digits of precision and retaining twenty-two.
It has no unresolved residues and agrees with direct exact rational
recurrence values through index one hundred.

For example, at \(n=7786\), whose three free digits are all two,
the three companion valuations are \((-5,-6,-4)\), and the multiplier
valuations are \((2,0,2)\). The selected index is \(7787\), with
\(v_5(Q_{7787})=6\); (2) already forces a negative companion
valuation at this word length. These numerical values are supporting
checks and are not used in the proof of the infinite family.
