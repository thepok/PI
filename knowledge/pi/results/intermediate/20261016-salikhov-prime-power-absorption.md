# Growing five-adic divisibility of the Salikhov multiplier

Date: 2026-10-16. Labels: `proof sketch` and exact `experiment`.
No Lean verification or priority claim. This strengthens the modulo-five
multiplier support theorem to unbounded powers of five. The new conclusion
concerns the normalized integer multiplier \(q_n\). It does not assert growing
precision for the rational companion or the reduced denominator.

## Result

Use the normalization and [coefficient identity](20260906-salikhov-mod5-support.md#coefficient-extraction-and-exact-count)
of the preceding Salikhov note:
\[
 I_n=a_n+b_n\pi,\quad q_n=2^{2-\lfloor5n/2\rfloor}b_n\in\mathbb Z,
 \qquad A_n=[z^nw^{3n}]\frac{(2-w)^2}{D(w)-zF(w)},
\]
\[
 D=(2-w)^3,\quad
 F=(w-1)^2(32-112w+156w^2-100w^3+25w^4)^2.
\]
The exact relation is
\[
 q_n=(-1)^n2^{1-\lfloor5n/2\rfloor}A_n,
\]
so \(v_5(q_n)=v_5(A_n)\).

There is an explicit integer function \(A(M)\) satisfying
\[
 A(M)\sim\frac{\log M}{20\log\log M}
\]
such that, uniformly in positive integers \(u,d,M\) with \(5\nmid d\),
\[
 \boxed{
 \#\{0\le j<M:v_5(q_{u+dj})<A(M)\}
   =O\!\left(M^{\delta_5}(\log M)^\kappa\right),
 }
\]
where
\[
 \delta_5=\log_5(91/20)=0.941401480142464\ldots<1,
 \qquad \kappa=5\log_5(100/91)=0.292992599287682\ldots.
\]
All implied constants are independent of the progression. In particular,
the density of exceptions tends to zero even when the progression changes
with \(M\).

Here is the complete definition of the precision. For \(a\ge2\), let
\[
 h_a=\min\{h\ge1:4\cdot5^{h-1}\ge a-1\},\quad
 m_a=5^{h_a},\quad D_a=5h_a+100.
\]
Set
\[
 a_L=\max\bigl(\{a\ge2:4aD_a\le L\}\cup\{0\}\bigr),
 \qquad A(M)=a_{\lfloor\log_5 M\rfloor}.
\]
The constants are deliberately conservative. For example, the first
nonzero certified precision is \(a_{840}=2\); the result is an asymptotic
theorem, not a useful small-index search threshold.

For the binary weight family \(\mathcal G\) from the
[entropy-family theorem](20261016-salikhov-entropy-family.md), this also gives
a global density-one statement at a common growing precision:
\[
 \#\{n\in\mathcal G\cap[1,N]:Z(n)\ne(0,0)\text{ or }
       v_5(q_n)<A(\lfloor\sqrt N\rfloor)\}=O(N^\eta),
\]
\[
 \eta=\frac{11}{15}H(4/11)=0.6934842234\ldots
    <\gamma=\log_2\frac{1+\sqrt5}{2}=0.6942419136\ldots,
\]
where \(H(t)=-t\log_2t-(1-t)\log_2(1-t)\). Since
\(\#(\mathcal G\cap[1,N])\asymp N^\gamma\), the exceptional proportion
tends to zero. The common precision is asymptotic to
\(\log N/(40\log\log N)\). Section 7 proves this global statement;
Section 8 retains the stronger precision and both signs on selected blocks.

## 1. A denominator compatible with valuation and degree

Put \(t=w(2-w)\), and write
\[
 S_0=(2-w)^2,\quad
 F=(1-t)(32-56t+25t^2)^2,\quad F_0=(1-t)(32-56t)^2,
\]
\[
 Q=D-zF,\quad Q_0=D-zF_0,\quad \Delta=Q-Q_0=-z(F-F_0).
\]
Assign a monomial \(z^iw^j\) the weight \(j-3i\). The ordinary weighted
degree of \(Q_0\) is at most three, and that of \(S_0\) is two. Moreover,
\[
 F-F_0=50(1-t)(32-56t)t^2+625(1-t)t^4.
\]
Thus \(25\mid\Delta\), and every coefficient of \(\Delta\) satisfies
\[
 v_5(\text{coefficient})\ge \text{weight}-3. \tag{1}
\]
Indeed the two displayed terms, after multiplication by \(z\), have
weights at most five and seven and valuations at least two and four.

Fix \(a\ge2\), put \(m=m_a=5^h\), and \(s=m/5\). Then \(a\le m\)
and \(s+a-1\le m\). Modulo \(5^a\), the finite geometric expansion gives
\[
 \frac{S_0}{Q}\equiv\frac{S_{\mathrm{init}}}{Q_0^m},\qquad
 S_{\mathrm{init}}=
 \sum_{j=0}^{\lfloor(a-1)/2\rfloor}
 S_0(-\Delta)^jQ_0^{m-j-1}. \tag{2}
\]
Its numerator has \(z\)-degree less than \(m\). By (1), its coefficients
satisfy
\[
 v_5([z^iw^j]S_{\mathrm{init}})\ge j-3i-3m+1. \tag{3}
\]

The lower-degree denominator is essential to this estimate. The original
\(Q\) has high-weight coefficients divisible by 25, but the substitution
\((z,w)\mapsto(z^5,w^5)\) multiplies their weights without multiplying
their valuations. Using that denominator in the degree argument below
would give an invalid invariant.

## 2. Integral Cartier transitions with bounded denominator

Let \(\mathcal C_{d,e}\) select the monomials whose two exponents are
respectively \(d,e\pmod5\), remove those residues, and divide both
exponents by five. A carry \(c\in\{0,1,2\}\) specifies the coefficient
line \(3n+c\). For a digit \(d\in\{0,1,2,3,4\}\), set
\[
 e=(3d+c)\bmod5,\qquad c'=(3d+c-e)/5.
\]

The polynomial
\[
 R=\frac{Q_0^5-Q_0(z^5,w^5)}5
\]
has integral coefficients and weighted degree at most 15. Expanding the
negative power of \(Q_0^5=Q_0(z^5,w^5)+5R\) yields
\[
 \mathcal C_{d,e}\!\left(\frac S{Q_0^m}\right)
 \equiv\sum_{j=0}^{a-1}(-5)^j\binom{s+j-1}{j}
 \frac{\mathcal C_{d,e}(SR^j)}{Q_0^{s+j}}
 \pmod{5^a}. \tag{4}
\]
Because \(s+j\le m\), each denominator can be raised to \(Q_0^m\)
using a nonnegative power of \(Q_0\). This is an integral linear operation
on the numerator, so existing common powers of five never decrease.

There are two preserved bounds. First, if \(\deg_zS<m\), then the
\(j\)-th term of (4), after raising its denominator, has \(z\)-degree at
most
\[
 \left\lfloor\frac{m-1+5j-d}{5}\right\rfloor+(m-s-j)=m-1.
\]
Second, at carry \(c\) every reachable numerator satisfies
\[
 v_5([z^iw^j]S)\ge j-3i-3m-c+1. \tag{W_c}
\]
For the bookkeeping, consider a contribution to a coefficient whose
valuation after the explicit factor \(5^j\) is at most \(T\). Before
section its weight is at most
\[
 3m+c-1+(T-j)+15j.
\]
After section and multiplication by \(Q_0^{m-s-j}\), this is at most
\[
 3m+c'+\left\lfloor\frac{T-j-1}{5}\right\rfloor
 \le 3m+c'-1+T.
\]
Additional valuation in the binomial coefficient only improves the bound.
The same bound holds for sums of contributions, proving \((W_{c'})\).

## 3. The zero constant Laurent coefficient

The degree bound alone would allow an extra noncontracting monomial. The
following invariant removes it.

For a state \((S,c)\), work in the integral Laurent-series ring
\[
 \mathcal R=\mathbb Z_5[[z]]((w^{-1}))
\]
and define
\[
 H_c(z,w)=w^{-c}\frac{S(z/w^3,w)}{Q_0(z/w^3,w)^m}.
\]
This is well-defined: the leading term of the transformed denominator is
\[
 Q_0(z/w^3,w)=-(1+3136z)w^3+\text{lower powers of }w,
\]
and \(1+3136z\) is a unit in \(\mathbb Z_5[[z]]\).

The invariant is
\[
 [w^0]H_c(z,w)=0\pmod{5^a}. \tag{R_c}
\]
Equivalently, the differential \(H_c\,dw/w\) has zero residue at
infinity. Throughout the proof, the expression being calculated is the
constant Laurent coefficient, which is minus the conventional residue at
infinity.

For the initial state, the \(j\)-th term of (2), divided by \(Q_0^m\)
and transformed as above, gives the differential
\[
 \frac{t^2z^j(F-F_0)^j}{(t^3-zF_0)^{j+1}}\,dw. \tag{5}
\]
Its rational coefficient depends only on \(t=w(2-w)=1-(w-1)^2\).
It is therefore even in \(w-1\), so its Laurent expansion at infinity
has no term of degree minus one in \(w-1\). Translation preserves the
residue. Each term of (5) has zero residue, proving \((R_0)\).

Every digit operation preserves the invariant. For a monomial with
original exponents \(i,j\), the carry relation gives
\[
 \frac{j-e}{5}-3\frac{i-d}{5}-c'
       =\frac{j-3i-c}{5}. \tag{6}
\]
Thus the transformed Cartier operation is \(\mathcal C_{d,0}\): it
selects the \(z\)-residue \(d\) and the \(w\)-residue zero. In
\(\mathcal R\), the Frobenius denominator
\[
 Q_0(z^5/w^{15},w^5)^{-s-j}
\]
has only exponents divisible by five in both variables. The same
coefficient-section identity that proves (4) at the origin consequently
proves it in this infinity expansion. The new constant Laurent coefficient
is exactly the \(z\)-section of the old one, and remains zero.

Finally, if a numerator has common valuation \(v<a\), division by
\(5^v\) preserves the zero identity modulo \(5^{a-v}\). The denominator
is a unit after its leading power of \(w\) is removed, and all remaining
coefficients lie in \(\mathbb Z_5[[z]]\). There is no hidden division
by a nonunit in this step.

## 4. Return to a small modulo-five module

Suppose a reachable numerator has exact common valuation \(v<a\).
Divide by \(5^v\) and reduce modulo five. Since \(m=5^h\),
\[
 Q_0^m=Q_0(z^m,w^m)\quad\text{over }\mathbb F_5.
\]
Apply any \(h\) successive digit operations. Let \(A,B\in[0,m)\)
be their two numerical residue classes, and let \(c'\) be the new carry.
Then
\[
 3A+c=B+mc'.
\]
The resulting rational function has the form \(T(w)/Q_0\). The numerator
contains no \(z\), because \(\deg_zS<m\) forces any contributing
original \(z\)-exponent to equal \(A\).

If \(w^j\) contributes to \(T\), the pre-division bound \((W_c)\)
gives
\[
 mj+B\le3A+3m+c-1+v,
 \qquad j\le3+c'+\left\lfloor\frac{v-1}{m}\right\rfloor.
\]
Since \(v<a\le m\), this bounds \(\deg T\) by \(c'+3\).
If the top degree occurs, the constant Laurent coefficient of the
transformed rational function is
\[
 [w^0]\left(w^{-c'}\frac{T(w)}{Q_0(z/w^3,w)}\right)
   =-\frac{[w^{c'+3}]T}{1+3136z}.
\]
The preserved zero identity forces this coefficient to vanish. Hence
\[
 \boxed{T\in V_{c'}:=\{P\in\mathbb F_5[w]:\deg P\le c'+2\}.} \tag{7}
\]
This conclusion also includes \(T=0\), when the common valuation has
already increased. The zero Laurent coefficient is essential: the larger
space permitting degree \(c'+3\) contains states that the word 03 does
not annihilate.

## 5. Exact contraction in the small module

Modulo five, the denominator \(Q_0\) equals the original \(Q\). For
\(T\in V_c\), the digit operation is
\[
 T\longmapsto\operatorname{section}_{e}
        \left(TF_0^dD^{4-d}\right),\qquad
 e=(3d+c)\bmod5,\quad c'=\lfloor(3d+c)/5\rfloor. \tag{8}
\]
The degree is at most
\[
 \left\lfloor\frac{c+2+6d+3(4-d)-e}{5}\right\rfloor=c'+2,
\]
so these spaces are invariant. Direct polynomial calculation shows that
the two-digit word 03, read least-significant digit first, kills every one
of the 12 basis states
\[
 (w^j,c),\qquad 0\le c\le2,\quad0\le j\le c+2.
\]

For the stronger quantitative bound, exhaust all digit orbits from these
12 states. There are exactly 111 states, including the three zero-numerator
states with their different carries. Let \(M_0\) be the nonnegative
transition-count matrix, retaining digit multiplicities. Let \(v_0\)
indicate the nonzero-numerator states and put \(v_2=M_0^2v_0\).
The [exact certificate](../../../../workflows/experiments/salikhov_prime_power_20261016/certificate.json)
records all states, transitions, and the componentwise inequalities
\[
 5M_0v_2\le21v_2,\qquad
 9\le v_2(s)\le22\quad\text{for every nonzero state }s. \tag{9}
\]
The [checker](../../../../workflows/experiments/salikhov_prime_power_20261016/lifting_certificate.py)
reconstructs this certificate from (8) using exact finite-field arithmetic.

By positivity, (9) implies that each basis state survives on at most
\[
 \frac{22}{9}\left(\frac{21}{5}\right)^b
\]
words of length \(b\). A polynomial in \(V_c\) is a linear combination
of at most five basis monomials. If every contributing basis monomial is
killed by a word, their combination is killed as well. A union bound therefore
gives, uniformly over \(T\in V_c\), at most
\[
 13\left(\frac{21}{5}\right)^b \tag{10}
\]
surviving words. This finite certificate supplies an all-length bound;
it does not infer infinite behavior from a finite sequence of \(q_n\).

## 6. Growing precision and uniform arithmetic progressions

For the fixed precision \(a\), set
\[
 b=4h+100,\quad D=h+b=5h+100,\quad
 p_0=13(21/25)^b.
\]
A block of \(D\) digits first uses \(h\) arbitrary digits to return to
\(V_c\), then \(b\) digits for (10). At every state of common valuation
\(v<a\), at most a proportion \(p_0\) of these blocks fail to increase
the common valuation. No block decreases it.

For \(L\) digit positions, let \(B=\lfloor L/D\rfloor\). If
\(B\ge4a\), a path still nonzero modulo \(5^a\) can have fewer than
\(a\) successful blocks. Consequently its total count is at most
\[
 5^L\sum_{j=0}^{a-1}\binom Bj p_0^{B-j}
 \le5^L\bigl(2p_0^{3/4}\bigr)^B. \tag{11}
\]
This uses only the uniform conditional failure bound at every state;
it assumes no independence between successive blocks.

The exact rational inequalities
\[
 (21/25)^{12}\le(91/100)^{20},\qquad
 16\cdot13^3(21/25)^{300}\le(91/100)^{400}
\]
imply
\[
 16\cdot13^3(21/25)^{3b}\le(91/100)^{4D},
 \qquad2p_0^{3/4}\le(91/100)^D.
\]
Since \(DB>L-D\), (11) is at most
\[
 (100/91)^D(91/20)^L. \tag{12}
\]

Choose \(a=a_L\) from the definition in the result. Because
\(h_a=\log_5 a+O(1)\),
\[
 a_L\sim\frac{(\log5)L}{20\log L},\qquad
 (100/91)^{D_a}=O(a_L^\kappa).
\]
If a length-\(L\) low-digit prefix has a zero numerator modulo \(5^a\),
every extension does also, and its final coefficient \(A_n\), hence
\(q_n\), vanishes modulo \(5^a\).

Now take \(L=\lfloor\log_5 M\rfloor\) in a progression \(u+dj\)
with \(5\nmid d\). Each residue modulo \(5^L\) is visited at most
\(\lceil M/5^L\rceil\le5\) times. Thus (12), multiplied by at most
five, bounds all failures of \(5^{A(M)}\mid q_{u+dj}\). This proves the
uniform progression theorem.

## 7. Global density one in the binary weight family

Define, as in the [entropy-family theorem](20261016-salikhov-entropy-family.md),
\[
 \mathcal G=\{2^km:k\ge2,\ m\ge1\text{ odd},\ s_2(3m)\le k\}.
\]
That theorem gives \(\#(\mathcal G\cap[1,N])\asymp N^\gamma\), with
\(\gamma=\log_2((1+\sqrt5)/2)\). Set
\[
 L=\lfloor\log_2(3N)\rfloor,\quad
 K=\lfloor4L/15\rfloor,\quad J=\lfloor2L/5\rfloor.
\]
We bound failures of the common precision
\(B_N=A(\lfloor\sqrt N\rfloor)\) in three ranges.

For \(k\le K\), bound all members of \(\mathcal G\), including the
failures. Writing \(r=3m\), its binary length is at most \(L+1-k\)
and its weight is at most \(k\). The Bernoulli weight \(\alpha=4/11\)
gives the same tilted count as the entropy-family proof:
\[
 \#\{r\text{ in this range}\}
 \le(11/7)^{L+1}(49/44)^k.
\]
Since \(49/44>1\), summing geometrically for \(k\le K\) gives
\[
 O\!\left((11/7)^L(49/44)^{4L/15}\right)=O(N^\eta),
 \qquad\eta=\frac{11}{15}H(4/11). \tag{13}
\]

For \(K<k\le J\), drop the binary weight condition. Odd \(m\) with
\(2^km\le N\) form an arithmetic progression in \(n\) of step
\(2^{k+1}\), and its length \(M_k\) satisfies
\[
 M_k\asymp N/2^k\gg N^{3/5}\ge\lfloor\sqrt N\rfloor
\]
for all sufficiently large \(N\). Because \(A\) is nondecreasing,
each failure of precision \(B_N\) is also a failure of precision
\(A(M_k)\). The uniform progression bound, summed geometrically, gives
\[
 O\!\left(\sum_{K<k\le J}(N/2^k)^{\delta_5}(\log N)^\kappa\right)
 =O\!\left(N^{11\delta_5/15}(\log N)^\kappa\right).
\]
The exact integer inequalities
\[
 91^{35}<20^{35}5^{33},\qquad
 11^{385}>2^{363}4^{140}7^{245}
\]
prove \(\delta_5<33/35<H(4/11)\). Thus
\(11\delta_5/15<\eta\), and the strict exponent gap absorbs the
polylogarithmic factor.

For \(k>J\), even the total number of odd-multiplier indices is
\(O(N/2^J)=O(N^{3/5})\). This is smaller than \(O(N^\eta)\).
Combining the three ranges proves
\[
 \#\{n\in\mathcal G\cap[1,N]:v_5(q_n)<B_N\}=O(N^\eta). \tag{14}
\]

The function \(H(t)/(1+t)\) is strictly increasing up to
\(p=(3-\sqrt5)/2\), where its unique maximum is \(\gamma\).
Since \(3/10<4/11<p\), the previously established \(Z\ne0\)
exceptional exponent \((10/13)H(3/10)\) is smaller than \(\eta\),
and \(\eta<\gamma\). Adding those exceptions to (14) proves the
global statement in the result, with relative exceptional proportion
\(O(N^{\eta-\gamma})\). All retained indices also retain the binary
reduced-numerator bounds inherited on every member of \(\mathcal G\).

## 8. Corollary on both signed entropy-family populations

Keep the notation and computable good indices of the
[entropy-family theorem](20261016-salikhov-entropy-family.md):
\[
 p=\frac{3-\sqrt5}{2},\quad\gamma=\log_2\frac{1+\sqrt5}{2},\quad
 \ell_k=\lfloor k/p\rfloor,\quad N_k=2^{k+\ell_k},
\]
\[
 \mathcal G_k^*=\{2^km:m\text{ odd},\ 0<3m<2^{\ell_k},\ s_2(3m)\le k\},
 \qquad a_k^*=a_{\lfloor\ell_k\log_5 2\rfloor}.
\]
For every sufficiently large good \(k\), each sign
\(\sigma\in\{-1,+1\}\) has
\[
 \#\{n\in\mathcal G_k^*: Z(n)=(0,0),\
       \ v_5(q_n)\ge a_k^*,\ \sigma(\pi-R_n)>0\}
    \gg\frac{N_k^\gamma}{\sqrt{\log N_k}}. \tag{15}
\]
The eventual lower bound of \(1/1000\) of \(\mathcal G_k^*\) for each
sign also survives. The precision tends to infinity, with
\[
 a_k^*\sim
 \frac{\log N_k}{20(1+p)\log\log N_k}.
\]
All these indices retain the established binary conclusions for the reduced
approximant \(R_n=P_n/Q_n\), \(Q_n>0\):
\[
 Q_n\text{ odd},\qquad
 v_2(P_n)\ge2n-1-2\lfloor\log_2 n\rfloor.
\]

To prove (15), embed the whole block in the odd-multiplier progression of
length \(2^{\ell_k}\), with step \(2^{k+1}\). The new theorem deletes
at most
\[
 O\!\left(2^{\delta_5\ell_k}\ell_k^\kappa\right)
\]
indices. The existing \(Z=0\) restriction deletes
\(O(2^{\delta\ell_k})\), where \(\delta<0.881\). Each sign already
has a robust core population of order
\(2^{H(p)\ell_k}/\sqrt{\ell_k}\).
The strict exponent comparison can be checked without decimals:
\[
 91^{20}<20^{20}5^{19},\qquad2^{82}>3^{15}5^{25}
\]
give \(\delta_5<19/20<H(3/8)<H(p)\), since \(3/8<p<1/2\).
Both deleted populations are therefore negligible. The actual-\(\pi\)
signed asymptotic and its fixed cosine margins are exactly those proved
in the linked predecessor; no assertion about generic replacement
constants enters this arithmetic step.

## Verification and scope

The two exact modular evaluators use different denominator representations:

- [prime_power.py](../../../../workflows/experiments/salikhov_prime_power_20261016/prime_power.py)
  uses \(Q^{5^{a-1}}\) and the direct prime-power Frobenius congruence.
- [bounded_cartier.py](../../../../workflows/experiments/salikhov_prime_power_20261016/bounded_cartier.py)
  implements (2) and (4), with denominator exponent \(m_a=O(a)\).
- [lifting_certificate.py](../../../../workflows/experiments/salikhov_prime_power_20261016/lifting_certificate.py)
  checks the complete small-state graph, the killing word, all entries of
  (9), and the rational inequalities used above.

Both modular evaluators agree with the exact published rational recurrence
modulo 125 through \(n=100\). The bounded-denominator evaluator also agrees
modulo 3125 through \(n=60\). In the latter check, the entire numerator
state becomes zero after five copies of the word 03, modulo 3125. This
illustrates absorption; the all-precision argument is Sections 1–6, not
an extrapolation of those samples.

From the repository root, run:

```sh
python3 workflows/experiments/salikhov_prime_power_20261016/lifting_certificate.py --json workflows/experiments/salikhov_prime_power_20261016/certificate.json
python3 workflows/experiments/salikhov_prime_power_20261016/prime_power.py --precision 3 --check 100
python3 workflows/experiments/salikhov_prime_power_20261016/bounded_cartier.py --precision 3 --check 100
python3 workflows/experiments/salikhov_prime_power_20261016/bounded_cartier.py --precision 5 --check 60
```

The finite computations are `experiment`; the infinite argument remains
a `proof sketch` and uses the inherited coefficient identity, binary
arithmetic, and actual-\(\pi\) asymptotic. The new five-adic information is
the growing common divisibility of the normalized multiplier \(q_n\).
For the normalized companion
\(v_n=5^{s_n}c_n\), \(s_n=\lfloor\log_5(4n)\rfloor\), cancellation
in the reduced rational approximant still depends on
\[
 v_5(Q_n)=\max(0,s_n+v_5(q_n)-v_5(v_n)).
\]
No estimate for that difference is proved here. In (15) the companion is
still only known to be zero modulo five. A nonzero five-adic unit class,
other denominator primes, and ordered decimal residues remain uncontrolled.
There is no E, CW0, CW9, or V1 conclusion.

Sources: the linked predecessor notes, the published
[Zeilberger–Zudilin integral](https://arxiv.org/html/1912.06345v2), and its
[exact recurrence](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt).
