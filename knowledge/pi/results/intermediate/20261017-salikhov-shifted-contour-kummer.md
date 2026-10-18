# A Kummer carry budget for a shifted Salikhov contour

Date: 2026-10-17. Status: `proof sketch`, with a separate exact `experiment`.
No Lean verification, decimal-word theorem, or priority claim is made.

The [third-contour theorem](20261017-salikhov-casoratian-non-cancellation.md)
constructs the actual rational source coefficients \(a_n,b_n,d_n\), their
nonzero Casoratian, and their rational endpoint primitive \(F_n\). This
note improves its third-column denominator budget. The change is made in
\(\mathbb Q_5\) and leaves the original rational Casoratian unchanged.

The accompanying [audit](../../../../workflows/experiments/salikhov_shifted_contour_kummer_20261017/audit.py) and
[certificate](../../../../workflows/experiments/salikhov_shifted_contour_kummer_20261017/certificate.json) check the new
coefficient identity and its valuation consequences. The source contour
and recurrence certificates remain those of the predecessor theorem.

## 1. The universal bound

Choose the unique root \(\iota\in\mathbb Z_5\) satisfying
\(\iota^2=-1\) and \(\iota\equiv2\pmod5\). Put
\[
 \beta=-1+2\iota,\qquad
 \widetilde d_n=d_n+\iota a_n
                 =2(-1)^n F_n(\beta).
 \tag{1}
\]
The last equality is the actual complex endpoint identity, evaluated at
the five-adic embedding. In particular it does not introduce a new
formal recurrence solution.

For every integer \(n\ge1\), define
\[
 L=\lfloor\log_5(4n)\rfloor,\qquad
 H=\lfloor\log_5(2L+1)\rfloor,
\]
\[
 K_L(n)=\#\left\{1\le r\le L:
        2n\bmod5^r<\frac{5^r+1}{2}\right\}.
 \tag{2}
\]
An empty count is zero. Then
\[
 \boxed{
 v_5(\widetilde d_n)
 \ge 1-\max\{H,L-K_L(n)\}.
 }
 \tag{3}
\]
All quantities on the right are explicit functions of the index. The
carry term is the new gain. The older rational-column bound was
\(v_5(d_n)\ge-L\).

For example, the carry term vanishes at \(n=7,32\), where the shifted
column really has valuations \(-1,-2\). Thus universal integrality of
\(\widetilde d_n\) would be false. Bound (3) retains the actual possible
poles and describes when their order is smaller.

## 2. The endpoint separates integral terms from the polynomial primitive

The predecessor's pole coefficients satisfy
\[
 \eta_{n,j}=5^{-j}A_{n,j}\in\mathbb Z[1/2],
 \qquad1\le j\le3n.
\]
At the chosen embedding,
\[
 \frac5{5-\beta}=\frac{3+\iota}{4},\qquad
 \frac5{5+\beta}=\frac{2-\iota}{2}.
 \tag{4}
\]
Both ratios have valuation exactly one. For instance
\((3+\iota)(3-\iota)=10\) and \(3-\iota\) is a unit, while
\((2-\iota)(2+\iota)=5\) and \(2+\iota\) is a unit.

Consequently the pole contribution
\[
 U_n=2(-1)^n\sum_{j=1}^{3n}\frac{\eta_{n,j}}{j}
 \left[\left(\frac{3+\iota}{4}\right)^j
       -\left(\frac{2-\iota}{2}\right)^j\right]
 \tag{5}
\]
has \(v_5(U_n)\ge1\), since \(j-v_5(j)\ge1\).

For the polynomial part put
\[
 \Gamma_{n,k}=[z^k]
   (1+6z+25z^2)^{2n}(1-25z)^{-3n-1}
   \in\mathbb Z,
 \qquad0\le k\le2n-1.
 \tag{6}
\]
The exact endpoint formula is
\[
 \boxed{
 \widetilde d_n
 =U_n-10\sum_{k=0}^{2n-1}
       \Gamma_{n,k}
       \frac{\beta^{4n-1-2k}}{4n-1-2k}.
 }
 \tag{7}
\]
To see the polynomial normalization directly, expand the source rational
integrand at infinity:
\[
 \mathcal R_n(x)
 =5(-1)^{n+1}x^{4n-2}
   (1+6x^{-2}+25x^{-4})^{2n}
   (1-25x^{-2})^{-3n-1}.
\]
Its nonnegative powers give (6); integration and the factor \(2(-1)^n\)
in (1) give the factor \(-10\) in (7). Also \(\beta\equiv3\pmod5\),
so every displayed power of \(\beta\) is a unit.

## 3. Deep integration denominators have an uncancelled leading coefficient

Fix \(k\) in (6), and write
\[
 j=4n-1-2k,\qquad m=2n-k=\frac{j+1}{2},\qquad r=v_5(j).
\]
The key coefficient statement is
\[
 \boxed{
 5^r>2L+1
 \quad\Longrightarrow\quad
 v_5(\Gamma_{n,k})=v_5\binom{2n}{k}.
 }
 \tag{8}
\]
It is an equality, so the possible cancellation among the coefficient
terms is resolved.

Expand (6) by taking \(u\) factors \(25z^2\) and \(v\) powers from
the denominator. Its nonzero summands are
\[
 A_{u,v}=25^{u+v}
   \binom{2n}{u}\binom{2n-u}{k-2u-v}
   6^{k-2u-v}\binom{3n+v}{v},
 \quad u,v\ge0,\quad2u+v\le k.
 \tag{9}
\]
The leading summand is
\(A_{0,0}=\binom{2n}{k}6^k\). Its valuation is at most \(L\):
Legendre's formula expresses the binomial valuation as a sum of zeros
and ones over at most \(\lfloor\log_5(2n)\rfloor\le L\) levels.

Let \(R=u+v>0\). If \(R\ge L\), every factor of the unnormalized
summand (9), except its explicit power of five, is an integer. Hence
\[
 v_5(A_{u,v})\ge2R\ge2L>L\ge v_5(A_{0,0}).
 \tag{10}
\]
Here \(L\ge1\); the hypothesis in (8) is impossible when \(L=0\).

For \(1\le R<L\), divide (9) by its leader:
\[
 \frac{A_{u,v}}{A_{0,0}}
 =25^R6^{-(2u+v)}
   \frac{k(k-1)\cdots(k-2u-v+1)}
        {u!(m+1)(m+2)\cdots(m+R)}
   \binom{3n+v}{v}.
 \tag{11}
\]
Because \(2(m+t)=j+2t+1\) and
\(0<2t+1<2L+1<5^r\),
\[
 v_5(m+t)=v_5(2t+1),\qquad1\le t\le R.
\]
Therefore
\[
 v_5\!\left(\prod_{t=1}^R(m+t)\right)
 =v_5((2R+1)!)-v_5(R!).
 \tag{12}
\]
Since \(u\le R\), adding the loss from \(u!\) is bounded above by
\(v_5((2R+1)!)\le R/2\). The remaining numerator factors in (11)
are integers. It follows that
\[
 v_5(A_{u,v}/A_{0,0})\ge2R-R/2>0.
 \tag{13}
\]
Thus every nonleading summand has strictly greater valuation. This
proves (8), uniformly in the moving index and in every allowed pair
\((u,v)\).

## 4. Kummer carries give the denominator budget

For any \(1\le s\le r\), the odd number \(j\) is divisible by
\(5^s\), so
\[
 m\bmod5^s=\frac{5^s+1}{2}.
\]
The summand in Legendre's formula for
\(v_5\binom{2n}{m}\) equals one precisely when
\((2n\bmod5^s)<(m\bmod5^s)\). Hence
\[
 v_5\binom{2n}{k}
 =v_5\binom{2n}{m}\ge K_r(n).
 \tag{14}
\]
Also \(r-K_r(n)\) is nondecreasing as \(r\) increases: each new
level adds either zero or one.

Now inspect each polynomial term in (7). If \(r\le H\), its valuation
is at least \(1-H\) by integrality of \(\Gamma_{n,k}\). If \(r>H\),
then (8) applies, and (14) gives
\[
 1+v_5(\Gamma_{n,k})-r
 \ge1-r+K_r(n)
 \ge1-L+K_L(n),
 \tag{15}
\]
because \(j<4n\) implies \(r\le L\). The pole part has valuation at
least one. Taking the minimum proves (3).

## 5. Transfer to the original consecutive triples

For \(n\equiv36\pmod{125}\), use six open interval states with endpoints
\[
 0,\ \frac14,\ \frac13,\ \frac12,\ \frac23,\ \frac34,\ 1.
\]
At level \(s\ge3\), the state records
\((n\bmod5^s)/5^s\). The Casoratian cost vector and the new carry
indicator are respectively
\[
 c=(0,1,2,-1,0,1),\qquad
 \kappa=(1,0,0,1,1,0).
 \tag{16}
\]
The cost vector can be read directly from the predecessor's factorial
formula. For \(M=5^s\), none of its fixed index shifts crosses a
multiple of \(M\): the residues of \(n,2n,3n,4n\) modulo 125 are
\(36,72,108,19\), and their largest positive shifts are only
\(2,4,5,8\). Its floor contribution consequently reduces to
\[
 E_M(n)=4\lfloor2x\rfloor-\lfloor4x\rfloor-\lfloor3x\rfloor,
 \qquad x=(n\bmod M)/M,
\]
whose negative is the stated vector \(c\).
The carry indicator follows directly from (2): since \(5^s\equiv1\pmod4\),
the inequality there is equivalent to the normalized residue lying in
\([0,1/4)\cup[1/2,3/4)\).

Suppose a sequence of appended digits starts and ends in state one,
and let \(\ell\) be the number of appended digits. Put
\[
 L=3+\ell,\qquad
 C=\sum_{\text{appended states}}c,\qquad
 K=\sum_{\text{appended states}}\kappa,\qquad
 S=C+K-\ell.
 \tag{17}
\]
The endpoint state makes the same denominator height \(L\) apply to
all three indices \(n,n+1,n+2\). The fixed prefix gives the low-level
carry counts \((1,0,2)\) at these offsets. All higher carry indicators
are unchanged by the offsets: the residues of \(2n\) and \(4n\)
modulo 125 stay a positive distance from the relevant boundaries after
adding at most four or eight. Thus
\[
 K_L(n),K_L(n+1),K_L(n+2)=(K+1,K,K+2).
 \tag{18}
\]
If
\[
 L-K\ge\max\{1,\lfloor\log_5(2L+1)\rfloor\},
 \tag{19}
\]
the universal bound (3) yields the common estimate
\[
 \min_{0\le r\le2}v_5(\widetilde d_{n+r})\ge1-L+K.
 \tag{20}
\]

The fixed low prefix has floor contributions \(-1\) at levels one,
two, and three, and the polynomial factor in the Casoratian is a
five-adic unit. Ending in state one makes every floor contribution
above level \(L\) vanish. The exact Casoratian therefore satisfies
\(v_5(W_n)=2-3-C=-1-C\). Replacing its third column by
\(\widetilde d=d+\iota a\) leaves its determinant exactly unchanged.
Expanding along the \(a\)-column, and using \(v_5(b_{n+r})\ge0\),
therefore gives
\[
 \min_{0\le r\le2}v_5(a_{n+r})
 \le(-1-C)-(1-L+K)=1-S.
 \tag{21}
\]
Select the least offset minimizing this rational valuation, as in the
predecessor theorem. The reduced original approximation at that offset
then has
\[
 \boxed{v_5(Q_{n+r(n)})\ge\max\{0,S-1\}.}
 \tag{22}
\]
The local net score is particularly simple:
\[
 \boxed{c+\kappa-1=(0,0,1,-1,0,0).}
 \tag{23}
\]
Digit complementation reverses this score. A separate counting argument
can use that symmetry to select many index paths satisfying (19).
Equations (19)--(22) give the exact arithmetic conclusion available for
such a selection. Reduced binary precision and actual approximation
signs require their respective arithmetic and phase inputs.

## 6. Exact audit and scope

The audit derives \(\Gamma_{n,k}\) through its generating function's
differential recurrence and checks that recurrence against the literal
two-parameter expansion. It then verifies 2,918 deep-denominator
coefficient equalities, 72,792 individual polynomial-term bounds, and
3,906 triple carry identities. These finite checks support the proof;
they do not replace its uniform estimates.

An independent source-recurrence calculation evaluates the actual
\(a_n,d_n\) exactly through \(n=1000\). A Hensel root modulo \(5^{50}\)
resolves every shifted-column valuation after the proved denominator
clearing. Bound (3) holds throughout and is sharp at 882 indices. The
audit also compares the complete endpoint formula (7), including its
pole contribution, with those source coefficients at the first twelve
positive indices.

From the repository root, the audit command is

```sh
python3 workflows/experiments/salikhov_shifted_contour_kummer_20261017/audit.py --json workflows/experiments/salikhov_shifted_contour_kummer_20261017/certificate.json
```

The source recurrence is imported from the existing local-pair audit;
no scratch-only input or numerical value of pi is needed.

The improvement concerns an actual source contour and an unchanged
nonzero determinant. The new coefficient statement is proved by a
unique least-valuation summand, rather than a noncancellation
assumption. The logarithmic branch in (3) is explicit and must still be
checked in any chosen digit family.

Nothing here orders the decimal residues of the selected rational
approximations. In particular (22) is a reduced denominator statement,
not a prescribed decimal-cylinder sign. It supplies no target word and
is not an admitted V1 candidate.
