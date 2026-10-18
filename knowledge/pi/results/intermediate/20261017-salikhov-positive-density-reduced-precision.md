# Positive-density simultaneous reduced precision at both actual signs

Date: 2026-10-17. Labels: `proof sketch` and `experiment`.
No Lean verification or priority claim is made.

The free-digit construction can use a fixed binary progression after
deleting an explicitly bounded set of exceptional residue classes. This
removes the logarithmic loss in its population. The sign selection now
uses only the irrationality of the fixed source phase.

## Result

Use the original modified Salikhov approximations
\[
 I_n=a_n+b_n\pi,\qquad
 R_n=-a_n/b_n=P_n/Q_n,\qquad Q_n>0,\quad(P_n,Q_n)=1.
\]
There is a constant \(c_*>0\) such that, for every sufficiently large
real \(X\) and each sign \(\sigma\in\{-1,+1\}\), at least
\[
 \boxed{c_*X}
 \tag{1}
\]
distinct original indices \(n\le X\) satisfy simultaneously
\[
 \boxed{
 \sigma(\pi-R_n)>0,\qquad Q_n\text{ odd},\qquad
 v_2(P_n)\ge2n-1-2\lfloor\log_2n\rfloor,
 }
\]
\[
 \boxed{v_5(Q_n)\ge\frac1{16}\sqrt{\log_5X}.}
 \tag{2}
\]
For the count of indices one may take
\[
 c_*=(2^{19}5^8)^{-1},
 \tag{3}
\]
with an unspecified sufficiently large threshold. The constructed sets
of indices have positive lower density. The prime precision and actual
sign belong to the same reduced rational pair at an individual index.

The published growing multiplier precision gives a further corollary:
at least \(c_*X/2\) indices of each sign satisfy the stronger bound
\[
 v_5(Q_n)\ge 2B(\lfloor X\rfloor)
                   +\frac1{16}\sqrt{\log_5X},
\]
where \(B\) is defined in Section 5 and
\(B(X)\sim7\log X/(150\log\log X)\).

The construction supplies no ordered decimal residue or prescribed
word. The main theorem V1 remains unresolved.

## 1. The three arithmetic inputs and the actual source phase

The [score-moment lemma](20261017-salikhov-score-moments.md) uses the six
interval states with destination score
\[
 g=(0,0,1,-1,0,0).
\]
For every \(N\ge1\), at least \(5^N/32\) raw digit words \(w\),
read from least to most significant and started in state zero, satisfy
\[
 |S_N(w)|\ge\frac{\sqrt N}{4}.
 \tag{4}
\]
This is a proved second- and fourth-moment estimate. The score process
has a bounded martingale correction; no limiting distribution is
assumed. A zero digit resets every state to zero; a four digit resets
every state to five. Complementing the digits and reflecting states
reverses the score. The three digits \([0,2,1]\) return every state
to state one and contribute exactly one score unit.

The [shifted-contour theorem](20261017-salikhov-shifted-contour-kummer.md) applies to a
returning digit path above the prefix \(36=121_5\). Put
\(L=\lfloor\log_5(4n)\rfloor\), let \(K_{\mathrm{car}}\) be the
number of its free carry indicators, and let \(S\) be its total
score. If
\[
 L-K_{\mathrm{car}}\ge
 \max\{1,\lfloor\log_5(2L+1)\rfloor\},
 \tag{5}
\]
then the least offset \(r(n)\in\{0,1,2\}\) minimizing
\(v_5(a_{n+r})\) satisfies
\[
 v_5(a_{n+r(n)})\le1-S,\qquad
 v_5(Q_{n+r(n)})\ge\max\{0,S-1\}.
 \tag{6}
\]
The original rational Casoratian and its shifted third column prove
this rule. All three indices have the same floor-log height. Since
score \(+1\) occurs only at the carry-zero state two, every such path
also satisfies
\[
 L-K_{\mathrm{car}}\ge S+3.
 \tag{7}
\]

The [fixed binary sieve](20261017-salikhov-fixed-binary-sieve.md) concerns
\[
 n=64m-3,\qquad m\equiv31\pmod{64}.
\]
It defines the sufficient deletion set
\[
 \mathcal E=\bigcup_{a=33,97,161,\ldots}
 \{m\ge1:m\equiv-a\pmod{2^{32a-7}}\}.
 \tag{8}
\]
For \(m\notin\mathcal E\), every member \(s=n,n+1,n+2\) of the
original triple satisfies
\[
 Q_s\text{ odd},\qquad
 v_2(P_s)\ge2s-1-2\lfloor\log_2s\rfloor,
 \tag{9}
\]
without a height restriction. On any progression
\(m_u=m_0+8000u\), \(0\le u<K\), of positive integers at most
\(Y\), with \(m_0\equiv31\pmod{64}\), the sieve gives
\[
 \#\{u:m_u\in\mathcal E\}
 \le\Delta K+J(Y),
 \quad
 \Delta=\frac{2^{-1043}}{1-2^{-2048}}<2^{-1042},
 \quad
 J(Y)=1+\lfloor\log_2(2Y)\rfloor.
 \tag{10}
\]
This conditional estimate is uniform in the start of the progression.

Finally, the original source approximation has the asymptotic
\[
 \pi-R_s=C_0\rho^s
 \bigl(\cos(s\theta+\varphi)+O(1/s)\bigr),
 \quad C_0>0,\quad0<\rho<1,
 \tag{11}
\]
with
\[
 0<\theta<\frac19,\qquad \theta/\pi\notin\mathbb Q.
 \tag{12}
\]
These exact source facts are established in the
[Casoratian phase argument](20261017-salikhov-casoratian-non-cancellation.md).
The argument below needs no Diophantine rate for (12).

## 2. Preserve a large score while reserving a free low block

For sufficiently large integers \(L\), set
\[
 k=\lceil2\log_5L\rceil,\qquad N=L-k-7.
 \tag{13}
\]
Thus \(L^2\le5^k<5L^2\), \(k=O(\log L)\), and \(N\sim L\).

For each raw word in (4), choose a pair \((e,w')\). If
\(S_N(w)>0\), take \(e=0,w'=w\); if \(S_N(w)<0\), take
\(e=4,w'=\bar w\). The high score following its reset digit is
\(|S_N(w)|\), independently of any earlier digits. The map is
injective, since \(e\) distinguishes its two branches. Let \(V\)
be the integer represented by the \(N\) digits of \(w'\).

For each \(0\le U<5^k\), form the index whose digits, from least
to most significant, are
\[
 [1,2,1,\ \text{the }k\text{ digits of }U,\ e,\ w',\ 0,2,1].
\]
In ordinary integer notation this is
\[
 n(U,e,V)=36+125\left(
 U+5^ke+5^{k+1}V
 +2\cdot5^{k+N+2}+5^{k+N+3}\right).
 \tag{14}
\]
Its total digit length is exactly \(L=N+k+7\). The final three
digits return to state one; in particular
\[
 \frac{5^L}{4}<n<\frac{5^L}{3}.
 \tag{15}
\]
The low block loses at most \(k\) score units, the reset prevents
that block from changing the high score, and the final three digits
add one. Hence every index in (14) satisfies
\[
 S\ge\frac{\sqrt N}{4}-k+1.
 \tag{16}
\]
Equations (7), (13), and (16) imply (5) once \(L\) is large.
The selected original index therefore has
\[
 v_5(Q_{n+r(n)})\ge\frac{\sqrt N}{4}-k
                         \ge\frac{\sqrt L}{8}.
 \tag{17}
\]
For the last inequality it suffices that \(N\ge3L/4\) and
\(k\le\sqrt L/16\), both eventual consequences of (13).

The selection uses the original triple literally: the prefix satisfies
\(36+125U+2<125\cdot5^k\), so offsets zero, one, and two cannot
carry into the reset digit. The common triple estimate in (6) applies
to all low choices without altering the high path.

## 3. Fixed-modulus sign selection and the local arithmetic deletion

Fix
\[
 M=4096,\qquad a_0=1981=64\cdot31-3.
\]
For any fixed high pair \((e,V)\), equation (14) has the form
\(n=n_0+125U\). The condition \(n\equiv a_0\pmod M\) retains
one residue class \(U=U_0+Mu\). Its exact length \(K_{e,V}\)
satisfies
\[
 K_{e,V}=\frac{5^k}{M}+O(1)\asymp L^2,
 \tag{18}
\]
uniformly in the high pair. The corresponding values
\(m=(n+3)/64\) are exactly
\[
 m=m_0+8000u,\qquad m_0\equiv31\pmod{64}.
 \tag{19}
\]
All are positive and less than \(5^L\).

The phases on this short progression advance by the fixed angle
\(125M\theta\). For each fixed nonzero integer Fourier mode
\(\ell\), irrationality in (12) and the geometric-sum formula give
\[
 \left|\sum_{u=0}^{K_{e,V}-1}
 e^{i\ell n(U_0+Mu,e,V)\theta}\right|
 \le\frac1{2\|125\ell M\theta/(2\pi)\|}<\infty.
 \tag{20}
\]
The right side is constant in \(L\), the high word, and the initial
phase. Division by (18) therefore tends to zero uniformly in every
high pair. Finite trigonometric approximation gives uniform interval
equidistribution of \(n\theta+\varphi\) on all these progressions.
Only fixed Fourier modes are used.

Take the fixed intervals
\[
 J_+=\left[-\frac\pi2+\frac\pi{20},
           \frac\pi2-2\theta-\frac\pi{20}\right],
 \qquad J_-=J_++\pi.
 \tag{21}
\]
Their relative length is \(9/20-\theta/\pi>2/5\). On \(J_+\),
all three cosines at offsets zero, one, and two are at least
\(\sin(\pi/20)>0\). On \(J_-\) they are at most
\(-\sin(\pi/20)\). The uniform asymptotic remainder in (11)
eventually preserves those signs, since every index is at least
\(5^L/4\). Thus each high pair supplies at least
\((2/5)K_{e,V}\) bases giving each actual sign at the selected
offset, before the binary deletion.

Apply (10) to (19), with \(Y=5^L\). At most
\[
 \Delta K_{e,V}+J(5^L)
 =\Delta K_{e,V}+O(L)
 \tag{22}
\]
bases are deleted. The bound is uniform in the high pair and makes
no assumption about correlation between a bad residue and a sign.
Subtracting the whole bound from either sign count leaves at least
\[
 \left(\frac25-\Delta-O(1/L)\right)K_{e,V}
 \ge\frac13K_{e,V}
 \tag{23}
\]
of each sign, for all sufficiently large \(L\). Every retained
selected index simultaneously satisfies (9) and (17).

## 4. A positive proportion at every cutoff

There are at least \(5^N/32\) admissible high pairs. For large \(L\),
equation (18) gives \(K_{e,V}\ge5^k/(2M)\). Thus each sign has
at least
\[
 \frac{5^N}{32}\frac{5^k}{6M}
 =\frac{5^{L-7}}{192M}
 \tag{24}
\]
selected original indices at scale \(L\). Both the high word and
the low block are counted; reserving the low digits creates no further
population loss.

The digit encoding is injective. Distinct bases are congruent to
36 modulo 125, so their triples are disjoint and selecting one offset
does not cause collisions. The intervals (15), including their two
possible extra offsets, are disjoint for different sufficiently large
\(L\). Their union defines fixed sets of selected indices for the
two actual signs.

Set \(X_L=\lfloor5^L/3\rfloor+2\). For a sufficiently large real
cutoff \(X\), choose the largest \(L\) with \(X_L\le X\). All
indices of that scale lie below \(X\), while maximality implies
\[
 5^L>\frac{3(X-2)}5,\qquad L>\log_5X-1.
 \tag{25}
\]
For \(X\ge4\), (24)--(25) give the lower bound
\[
 \frac{X}{640M5^7}
 =\frac{X}{2^{19}5^8},
\]
which proves (1) and (3). The depth in (17) satisfies
\[
 \frac18\sqrt L\ge\frac1{16}\sqrt{\log_5X}
\]
eventually, proving (2).

If distinct rational values, rather than distinct indices, are desired,
the count still has order \(X\). On the fixed sign margins (21),
equation (11) gives constants \(c_1,c_2>0\) such that
\[
 c_1\rho^s\le|\pi-R_s|\le c_2\rho^s
\]
for every sufficiently large selected index. Choose a fixed integer
\(D\) with \(c_2\rho^D<c_1\), and within each sufficiently large
scale greedily keep indices at least \(D\) apart. This loses at most
a fixed factor \(D\) and makes
their error magnitudes strictly decreasing, hence their reduced
rational values distinct. Every prime and depth bound is preserved.

## 5. Use the published multiplier depth twice

The [full-pair growing-precision theorem](20261017-salikhov-full-pair-growing-precision.md)
uses the explicit function
\[
 h_a=\min\{h\ge1:4\cdot5^{h-1}\ge a-1\},\qquad
 D_a=5h_a+100,
\]
\[
 a_r=\max\bigl(\{a\ge2:4aD_a\le r\}\cup\{0\}\bigr),
 \qquad
 B(M)=a_{\lfloor14\lfloor\log_5M\rfloor/15\rfloor}.
 \tag{26}
\]
It proves, in particular,
\[
 \#\{1\le s\le M:v_5(q_s)<B(M)\}=O(M^{52/55}),
 \qquad B(M)\sim\frac{7\log M}{150\log\log M}.
 \tag{27}
\]
Its multiplier normalization differs from \(b_s\) by a power of two,
so \(v_5(b_s)=v_5(q_s)\).

Take \(M=\lfloor X\rfloor\) and put \(B=B(M)\). Delete every
constructed triple containing any index in the exceptional set in
(27). Every member of every triple at the chosen scale is at most
\(M\), by the definition of \(X_L\). Distinct bases have disjoint
triples, so the number of deleted bases is at most the number of
exceptional indices, namely \(O(M^{52/55})=o(X)\). This leaves at
least \(c_*X/2\) selected indices of each sign for sufficiently large
\(X\). Every retained triple satisfies
\[
 v_5(b_n),\ v_5(b_{n+1}),\ v_5(b_{n+2})\ge B.
\]

The same shifted third column used in (6) has the common bound
\(v_5(\widetilde d_{n+r})\ge1-L+K_{\mathrm{car}}\). Every
product in every cofactor of the expansion along the \(a\)-column
contains one \(b\)-entry and one shifted third-column entry. Consequently,
writing \(W_n\) for the unchanged Casoratian, the non-Archimedean
triangle inequality gives
\[
 v_5(W_n)\ge
 \min_{0\le r\le2}v_5(a_{n+r})+B+1-L+K_{\mathrm{car}}.
\]
The exact relation already used in (6) is
\(v_5(W_n)-(1-L+K_{\mathrm{car}})=1-S\). Hence the same
least minimizing offset \(r(n)\), without any new selection, has
\[
 v_5(a_{n+r(n)})\le1-S-B
 \le k-\frac{\sqrt N}{4}-B
 \le-B-\frac{\sqrt L}{8}.
 \tag{28}
\]
For every remaining selected index \(s=n+r(n)\), the reduced-pair
valuation identity therefore gives
\[
 v_5(Q_s)=v_5(b_s)-v_5(a_s)
 \ge2B(\lfloor X\rfloor)+\frac{\sqrt L}{8}
 \ge2B(\lfloor X\rfloor)+\frac1{16}\sqrt{\log_5X}.
 \tag{29}
\]
The equality uses \(v_5(a_s)<0\le v_5(b_s)\), so the reduced
numerator is a five-adic unit. The first copy of \(B\) improves
the determinant bound on the companion; the second belongs to the
selected multiplier itself. All binary and actual-sign conclusions
remain in force. The deletion in this corollary is a global cardinality
bound; it requires no independence from the earlier selection.

## 6. Proof status, reproduction, and remaining gap

The every-cutoff population assertion follows from the exact arithmetic inputs,
the moment bound, the uniform fixed-step geometric sum, and the local
exception count. Its eventual threshold is not evaluated; it depends
on the fixed phase and the source asymptotic remainder. No
Diophantine approximation rate for that phase is used.

The [exact audit](../../../../workflows/experiments/salikhov_positive_density_precision_20261017/audit.py)
and its [deterministic certificate](../../../../workflows/experiments/salikhov_positive_density_precision_20261017/certificate.json)
check the encoding, reset independence,
literal fixed low progressions, their exact 8000-step normalization,
the Casoratian and carry transfer, and the arithmetic deletion on
large integer examples, including examples beyond the first possible
exceptional modulus. There are 17 high pairs and 52 complete triple
checks. One admissible high word has a 95-term low progression that
actually meets the first exceptional class; every position of that
progression is checked directly. These checks do not infer asymptotic
signs or densities from a finite sample.

From the repository root, run:

```sh
python3 workflows/experiments/salikhov_positive_density_precision_20261017/audit.py --json workflows/experiments/salikhov_positive_density_precision_20261017/certificate.json
```

Positive density here concerns indices of actual pi approximants. The
theorem does not control the ordered unit residue of a reduced pair
modulo a decimal power. It therefore supplies no occurrence of a
specified decimal word and does not establish V1.
