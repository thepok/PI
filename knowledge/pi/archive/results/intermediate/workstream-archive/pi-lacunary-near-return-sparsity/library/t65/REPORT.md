# T65: removing the power-of-5 transient in the T63 rational phases

Date: 2026-08-06 UTC.

Claim status: **proof sketch**.  The orbit decompositions and inequalities below
are elementary exact arithmetic.  The Bailey--Crandall statement is checked
against the pinned primary source.  No assertion of normality,
equidistribution, FSFS, C1, C2, or the canonical fixed-pi estimate is made.

## 1. Scope, statement pin, and quantifiers

The canonical statement at
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

It asks, with ordered pairs and the diagonal included, whether for every
integer `A >= 1`, every sufficiently large `n` admits an `N` such that

\[
 A n Q_\pi(n,N)\le N^2.
\tag{1.1}
\]

This note does not alter those quantifiers and does not prove (1.1).  It audits
one proposed sufficient route: replace a finite collection of decimal-ray
phases by rational phases obtained from the Zudilin truncations pinned in T63,
remove their powers of 5, and then try Bailey--Crandall (2002), Theorem 4.6 on
the remaining coprime orbit.

The quantifiers in the arithmetic audit are explicit.  Unless a later section
adds hypotheses,

\[
 e,J\in\mathbb N,\quad m\ge1,\quad (m,10)=1,
 \quad a\in\mathbb Z,\quad (a,5m)=1.
\tag{1.2}
\]

The denominator `5^e m` is therefore reduced.  Orbit frequencies `h` are
arbitrary nonzero integers.  The cases `J=0`, `e=0`, `m=1`, and `J<=e` are not
suppressed.  Here and below

\[
 \mathbf e(x)=\exp(2\pi i x),\qquad
 S_J(h;a,e,m)=\sum_{j=0}^{J-1}
   \mathbf e\!\left({ha10^j\over5^e m}\right).
\tag{1.3}
\]

## 2. Exact orbit decomposition for all `e,J`

### 2.1 The requested `e`-step split

Put `r=min(e,J)`.  Directly separating indices below and above `e` gives

\[
\boxed{
 S_J(h;a,e,m)=
 \sum_{j=0}^{r-1}\mathbf e\!\left({ha10^j\over5^e m}\right)
 +{\bf1}_{J>e}\sum_{t=0}^{J-e-1}
   \mathbf e\!\left({ha2^e10^t\over m}\right).}
\tag{2.1}
\]

Indeed, for `j=e+t`,

\[
 {ha10^{e+t}\over5^e m}={ha2^e10^t\over m}.
\tag{2.2}
\]

Thus the first `min(e,J)` iterates are the power-of-5 transient and, exactly
when `J>e`, the remaining length is

\[
 L=J-e.
\tag{2.3}
\]

For the base phase `h=1`, every index `j<e` has reduced denominator
`5^(e-j)m`, so these are genuinely noninvertible base-10 iterates.  The tail
has denominator `m`, which is coprime to 10.  If `J<=e`, the tail is empty;
there is no Bailey--Crandall sum to estimate.  If `m=1`, every tail term is 1,
so its sum is exactly `L`, not cancellative.

### 2.2 Frequency-dependent early reduction

T55 and T61 use moving integer frequencies.  A frequency divisible by 5 can
shorten the minimal transient, so (2.1) must not be misreported as a
lowest-terms decomposition for every `h`.

Let

\[
 s=v_5(|h|),\quad g=(|h|,m),\quad M={m\over g},
 \quad h=5^s g u,
 \quad \tau=(e-s)_+.
\tag{2.4}
\]

Then `(u,5M)=1`.  The reduced denominator of the `j`th phase in (1.3) is

\[
 q_j=M5^{\max(e-s-j,0)}.
\tag{2.5}
\]

For `0<=j<tau`, cancellation gives

\[
 {ha10^j\over5^e m}={au2^j\over5^{e-s-j}M}.
\tag{2.6}
\]

Set

\[
 H_\tau=au2^\tau5^{s+\tau-e}.
\tag{2.7}
\]

The exponent in (2.7) is nonnegative, `(H_tau,M)=1`, and for every `t>=0`,

\[
 {ha10^{\tau+t}\over5^e m}={H_\tau10^t\over M}.
\tag{2.8}
\]

Consequently the fully reduced form is

\[
\boxed{
 S_J=
 \sum_{j=0}^{\min(J,\tau)-1}
   \mathbf e\!\left({au2^j\over5^{e-s-j}M}\right)
 +{\bf1}_{J>\tau}\sum_{t=0}^{J-\tau-1}
   \mathbf e\!\left({H_\tau10^t\over M}\right).}
\tag{2.9}
\]

Equations (2.1) and (2.9) are both exact.  Equation (2.1) is the common
`e`-step bookkeeping split requested in the agenda; (2.9) records every
frequency cancellation that a literal theorem application must respect.

## 3. Bailey--Crandall Theorem 4.6, literally

The primary source is Bailey and Crandall, *Random Generators and Normal
Numbers*, Experimental Mathematics 11 (2002), Theorem 4.6, printed pp. 12--13;
the DOI, URL, and byte hash are in `SOURCE_PINS.md`.

For fixed coprime integers `b,c>1`, the theorem gives positive constants
`A,B,D`, depending only on `b,c`, such that for every positive `L`, all
sufficiently large exponents `nu`, and every integer `H` satisfying

\[
 (H,c^\nu)<Dc^\nu,
\tag{3.1}
\]

one has

\[
\boxed{
 \left|\sum_{t=0}^{L-1}
   \mathbf e\!\left({Hb^t\over c^\nu}\right)\right|
 <B\left(Ac^{\nu/2}+Lc^{-\nu/2}\right)\log(c^\nu).}
\tag{3.2}
\]

The final logarithm in the primary source multiplies both terms in
parentheses.  T63 equations (3.17) and (7.5) transcribed it only on the second
term.  This note uses the larger, source-faithful majorant (3.2).  The source
does not give numerical values for `A,B,D` or for the sufficiently-large
threshold.

### 3.1 Literal checklist for the post-transient tail

Apply (3.2) with `b=10` only after checking all of the following against the
tail modulus, never against the original noncoprime `5^e m`:

1. **Positive tail length:** `L=J-e>0` in (2.1), or
   `L_h=J-tau>0` in the reduced split (2.9).
2. **Coprime base:** `(10,m)=1`, or `(10,M)=1` after frequency reduction.
3. **Pure-power presentation:** the chosen post-transient modulus is
   `Q=c^nu` for one fixed integer `c>1` coprime to 10.  The integer `c` may be
   composite; "mixed prime" alone is not a failure.  If
   `Q=prod p^(alpha_p)`, such a presentation with `nu>=2` exists exactly when
   `nu` divides every `alpha_p`.
4. **Large exponent:** the same `nu` is at least the unspecified threshold
   `nu_0(10,c)`.  Writing an arbitrary `Q` as `Q^1` does not verify this.
5. **Frequency gcd:** using the common tail (2.1),

   \[
   H=ha2^e,\qquad (H,m)=(h,m)<Dm.
   \tag{3.3}
   \]

   Using (2.9), `(H_tau,M)=1`, but the concrete condition `1<DM` still has
   to hold.  It is automatic only after increasing a fixed-`c` large-exponent
   threshold, not for an unverified concrete exponent.
6. **Orbit length:** for a reduced tail with `M>1`, the exact period is

   \[
   T=\operatorname{ord}_M(10)\le\varphi(M)\le M.
   \tag{3.4}
   \]

   If `L=kT+r`, `0<=r<T`, then exactly

   \[
   \sum_{t<L}\mathbf e(H_\tau10^t/M)=
   k\sum_{t<T}\mathbf e(H_\tau10^t/M)
   +\sum_{t<r}\mathbf e(H_\tau10^t/M).
   \tag{3.5}
   \]

   Bailey--Crandall's proof uses the corresponding order modulo `c^nu` and
   handles arbitrary `L` by this complete-period-plus-remainder split.
7. **Nontrivial size:** (3.2) must improve on the trivial bound `L` at the
   actual target length and frequencies.

A nonminimal lift is logically possible but gives no free hypothesis.  If
`M` divides `Q=c^nu`, one can replace `H_tau/M` by
`(H_tau Q/M)/Q`.  Then

\[
 (H_\tau Q/M,Q)=Q/M,
\tag{3.6}
\]

so (3.1) becomes `1/M<D`, and the square-root cost is that of the larger `Q`.
All constants and the large-exponent threshold depend on the chosen `c`.

### 3.2 Exact nontriviality inequality

Write `Q=c^nu`.  Since the theorem's conclusion is strict, its displayed
majorant certifies an improvement over the trivial bound whenever

\[
 B\left(A\sqrt Q+{L\over\sqrt Q}\right)\log Q\le L.
\tag{3.7}
\]

This first requires

\[
 \sqrt Q>B\log Q,
\tag{3.8}
\]

and, under (3.8), is equivalent to

\[
\boxed{
 L\ge{BAQ\log Q\over\sqrt Q-B\log Q}.}
\tag{3.9}
\]

Paying for `tau` transient terms by the triangle inequality gives a strict
bound by `tau` plus the majorant in (3.2).  Condition (3.7) therefore certifies
a strict improvement over `J=tau+L`.  Along a fixed-`c` family, an `o(L)`
consequence from this bound requires

\[
 \sqrt Q\log Q=o(L),
\tag{3.10}
\]

not merely `sqrt(Q)=o(L)`.

## 4. The literal T55 and T61 ranges

This section uses the machine-checked T55 and T61 finite definitions, whose
hashes are pinned in `SOURCE_PINS.md`.  The orbit-sum rewrites below are direct
finite algebra, not claims imported from a sketch-level report.

Let

\[
 \mathcal T_H=\{u\in\mathbb N:\lfloor H/10\rfloor<u\le H\},
 \qquad H=R-1,
\tag{4.1}
\]

and let `C_q=(10^s-1)C_k`.  In the legal chain context used here,
`C_k>0`, `s>=1`, and hence `C_q>0`.

Write

\[
 w_R(v)=1-{v\over R},
\tag{4.1a}
\]

and define `gamma_u(theta)` recursively by

\[
 \gamma_0(\theta)=0,
 \qquad
 \gamma_u(\theta)=w_R(u)+p_u(\theta)\quad(u>0),
\tag{4.1b}
\]

where

\[
 p_u(\theta)=
 \begin{cases}
 \mathbf e(-9(u/10)C_q\theta10^\ell)\gamma_{u/10}(\theta),&10\mid u,\\
 0,&10\nmid u.
 \end{cases}
\tag{4.1c}
\]

These are T55's `triangularWeight`, `orbitCoefficient`, and
`predecessorCoefficient` at `beta=C_q theta`.  The recursion terminates because
`u/10<u`.  If `1<=u<=R-1` and `nu_10(u)` is the largest `a` with `10^a|u`,
then all displayed weights are nonnegative and repeated use of (4.1b) gives
the elementary bound

\[
 |\gamma_u(\theta)|\le
 \Gamma_u:=\sum_{a=0}^{\nu_{10}(u)}w_R(u/10^a).
\tag{4.1d}
\]

The T55 block factors as

\[
 \sum_{j=0}^{\ell-1}
 \mathbf e\bigl(C_qu(10^\ell-10^j)\pi\bigr)
 =\mathbf e(C_qu10^\ell\pi)S_\ell^\pi(-C_qu).
\tag{4.2}
\]

Thus T55 requires length and frequencies

\[
 J_{55}=\ell,\qquad
 \mathcal F_{55}=\{-C_qu:u\in\mathcal T_H\},
 \qquad |h|<C_qR.
\tag{4.3}
\]

The full weighted T55 terminal correlation is

\[
 T_{55}(\theta)=\sum_{u\in\mathcal T_H}\gamma_u(\theta)
 \mathbf e(C_qu10^\ell\theta)S_\ell^\theta(-C_qu).
\tag{4.3a}
\]

Suppose the transient plus Bailey--Crandall estimate gives a complete-sum
bound `F_(-C_q u)` as in Section 3.  Then

\[
 |T_{55}(\theta)|\le
 U_{55}:=\sum_{u\in\mathcal T_H}\Gamma_uF_{-C_qu}.
\tag{4.3b}
\]

The literal T55 lower-bound target is

\[
 \Theta_{55}={\ell\over8R\delta^2}-{\ell\over2}+B_{\rm end},
 \qquad
 B_{\rm end}=2\sum_{1\le v\le\lfloor(R-1)/10\rfloor}
 |\gamma_v(\pi)|.
\tag{4.3c}
\]

Thus cancellation estimates alone can imply T55's required
`Re(T_55(pi))>Theta_55` only after an approximation transfer and the explicit
aggregate inequality

\[
 U_{55}+E_{55}<-\Theta_{55}.
\tag{4.3d}
\]

In particular, this route requires `Theta_55<0`.  An exact Lipschitz error
budget for the fully expanded labeled sum is

\[
 E_{55}=2\pi|C_q||\pi-\theta|
 \sum_{u\in\mathcal T_H}\sum_{a=0}^{\nu_{10}(u)}\sum_{j<\ell}
 w_R(u/10^a)
 \left|(u/10^a)10^\ell-u10^j\right|.
\tag{4.3e}
\]

Every frequency in (4.3e) is integral.  Equation (4.3d), not merely a
nontrivial bound for one `S_ell`, is the replayable T55 aggregate requirement.

For T61 put

\[
 m_{u,j}=u(10^\ell-10^j),\qquad
 u\in\mathcal T_H,\quad0\le j<\ell.
\tag{4.4}
\]

Then

\[
 9u10^{\ell-1}\le m_{u,j}<u10^\ell<R10^\ell
\tag{4.5}
\]

and the exact telescope is

\[
 \mathbf e(C_k10^sm_{u,j}\pi)-\mathbf e(C_km_{u,j}\pi)
 =S_s^\pi(10C_km_{u,j})-S_s^\pi(C_km_{u,j}).
\tag{4.6}
\]

Hence

\[
 J_{61}=s,
\quad
 \mathcal F_{61}=\{C_km_{u,j},10C_km_{u,j}:u\in\mathcal T_H,j<\ell\},
\tag{4.7}
\]

with

\[
 |h|<10C_kR10^\ell,
 \qquad\hbox{endpoint scale }<C_k10^sR10^\ell.
\tag{4.8}
\]

For a rational phase with reduced denominator `5^e m`, the common
Bailey--Crandall tail lengths are therefore

\[
 L_{55}=(\ell-e)_+,
 \qquad L_{61}=(s-e)_+.
\tag{4.9}
\]

The minimally reduced lengths replace `e` by `(e-v_5(h))_+` separately for
every label.  A valid uniform T55 use must check, for every `u` in (4.3),

\[
 (C_qu,m)<Dm
\tag{4.10}
\]

and (3.7)--(3.9) at the resulting tail length.  For the paired T61 frequencies,
`(10h,m)=(h,m)`, but both sums in (4.6) remain present.

Even individual nontrivial bounds do not by themselves prove the T61 premise.
If `C_h` is a proved upper bound for a rational tail sum at frequency `h`, put
`F_h=tau_h+C_h`, where `tau_h` is the exact transient length from (2.4), paid
trivially.  The triangle inequality gives only

\[
 V_{\rm rat}\le
 \sum_{u\in\mathcal T_H}\sum_{j<\ell}w_R(u)
 \bigl(F_{C_km_{u,j}}+F_{10C_km_{u,j}}\bigr)^2,
\tag{4.11}
\]

after separately paying all transients.  This entire expression would have to
be below the literal T61 threshold

\[
 A_{\rm dir}=\sum_{u\in\mathcal T_H}\sum_{j<\ell}w_R(u),
\tag{4.11a}
\]

\[
 B_{\rm pred}=\left\|
 \sum_{u\in\mathcal T_H}\sum_{j<\ell}
 p_u(\pi)\mathbf e(C_qu(10^\ell-10^j)\pi)
 \right\|,
\tag{4.11b}
\]

with `B_end` as in (4.3c).  In this notation the threshold is

\[
 \ell+2A_{\rm dir}-2B_{\rm pred}-2B_{\rm end}
 -{\ell\over4R\delta^2},
\tag{4.12}
\]

with a strict margin large enough for rational-approximation error.  The
predecessor and endpoint budgets in (4.12) cannot be dropped.  No pinned source
provides (4.10), (4.11), or the strict margin uniformly over (4.3) and (4.7).

## 5. Corrected individual Zudilin summands

Zudilin v2, Section 3, printed p. 3, corrects the modular denominator omitted
in v1.  Let `n,d` be nonnegative integers, put `t=2n+1`, and set

\[
 t=2n+1=5^k m,\qquad k=v_5(t),\qquad (m,5)=1.
\tag{5.1}
\]

For either conjugate complex summand after multiplication by `10^d`,

\[
 Z_{n,d}^{\mp}={8\,10^d\over t(1\mp2i)^t},
\tag{5.2}
\]

rationalization gives exactly

\[
 Z_{n,d}^{\mp}
 ={2^{d+3}5^{d-k-t}(1\pm2i)^t\over m}.
\tag{5.3}
\]

Define

\[
 e_{n,d}=(t+k-d)_+,
 \qquad a_{n,d}=(d-k-t)_+.
\tag{5.4}
\]

Then the corrected common Gaussian denominator is displayed exactly by

\[
\boxed{
 Z_{n,d}^{\mp}
 ={2^{d+3}5^{a_{n,d}}(1\pm2i)^t\over5^{e_{n,d}}m}.}
\tag{5.5}
\]

In the flawed range `t>d-k`,

\[
 e_{n,d}=t+k-d=2n+1+k-d,
\tag{5.6}
\]

which is precisely the missing exponent identified by v2.  A subsequent
base-10 orbit has `min(e_(n,d),J)` displayed transient terms and, if
`J>e_(n,d)`, a tail of length `J-e_(n,d)` modulo `m`.

Bailey--Crandall is a scalar real rational-phase theorem, so the pi-producing
coordinate must be exposed.  Write `(1+2i)^t=x_t+iy_t`.  The recurrence in the
pinned source gives

\[
 y_t=2b_n,
\tag{5.7}
\]

and the imaginary part of the conjugate identity contributes the real scalar

\[
 r_n={16b_n\over t5^t}.
\tag{5.8}
\]

Indeed, `y_(2n+1)/2` and `b_n` have the same initial values `1,-1` and the
same recurrence with coefficients `-6,-25`, so (5.7) follows by induction.

After multiplication by `10^d`,

\[
 10^dr_n={2^{d+4}5^{d-k-t}b_n\over m}.
\tag{5.9}
\]

Moreover `b_0=1`, `b_1=-1`, and
`b_n=-6b_(n-1)-25b_(n-2)` imply inductively
`b_n=(-1)^n mod 5`.  Therefore 5 never cancels from (5.9).  At an additional
nonzero frequency `h`, the exact transient length and post-transient scalar
modulus are

\[
 \tau_{n,d,h}=(e_{n,d}-v_5(h))_+,
 \qquad M_{n,h}={m\over(m,hb_n)}.
\tag{5.10}
\]

Every modulus in (5.10) must separately pass the pure-power, large-exponent,
gcd, period, and nontriviality tests of Section 3.  The cofactors
`m=(2n+1)/5^k` vary with `n` and have unrestricted odd prime support; the
pinned construction supplies no fixed `c`, no large exponent, and no uniform
constants for these coordinate- and frequency-dependent divisors.

### 5.1 Why termwise cancellation cannot be combined

Let the real Zudilin truncation be

\[
 \pi_K=\sum_{n=0}^{K-1}r_n,
 \qquad r_n={16b_n\over(2n+1)5^{2n+1}}.
\tag{5.11}
\]

Then exactly

\[
 \mathbf e(h10^j\pi_K)=\prod_{n<K}\mathbf e(h10^jr_n).
\tag{5.12}
\]

Bounds for the separate sums over `j` of the factors in (5.12) do not bound the
sum over `j` of their product.  This is an algebraic obstruction, not a lack of
finite experimentation.  For any `J>=2`, let `z_j=exp(2 pi i j/J)`.  Then

\[
 \sum_{j<J}z_j=0,\qquad
 \sum_{j<J}\overline{z_j}=0,
 \qquad
 \sum_{j<J}z_j\overline{z_j}=J.
\tag{5.13}
\]

Thus perfect cancellation in two individual orbit sums can coexist with no
cancellation in their product.  A new multilinear theorem would be needed to
combine individual corrected summands.  Bailey--Crandall Theorem 4.6 is not
such a theorem.

## 6. The T63 common-denominator truncation

Let `K>=1` and set

\[
 x=2K-1,\qquad
 L_K=\operatorname{lcm}(1,3,5,\ldots,x),
\tag{6.1}
\]

and use T63's convenient common denominator

\[
 Q_K=5^xL_K.
\tag{6.2}
\]

For each odd prime `p<=x`, let

\[
 \alpha_p(K)=\max\{r\ge0:p^r\le x\}.
\tag{6.3}
\]

Then exactly

\[
 L_K=\prod_{\substack{p\le x\\p\text{ odd prime}}}p^{\alpha_p(K)},
\quad
 Q_K=5^{E_K}M_K,
\tag{6.4}
\]

where

\[
 E_K=x+\alpha_5(K),
\qquad
 M_K=\prod_{\substack{p\le x\\p\ne2,5}}
 p^{\alpha_p(K)}.
\tag{6.5}
\]

This corrects the tempting but incomplete statement that the 5-adic exponent
is merely `2K-1`: the lcm contributes `alpha_5(K)` more.  Prime powers enter
the post-transient cofactor at the exact thresholds

\[
 p^r\mid M_K
 \quad\Longleftrightarrow\quad
 p\ne2,5\ \hbox{ and }\ p^r\le2K-1.
\tag{6.6}
\]

For example,

\[
\begin{array}{c|c|c|c}
K&x&E_K&M_K\\ \hline
1&1&1&1\\
2&3&3&3\\
3&5&6&3\\
4&7&8&21\\
5&9&10&63\\
6&11&12&693
\end{array}
\tag{6.7}
\]

From `K=4` onward the displayed cofactor already contains both 3 and 7.
This mixed support is not itself disqualifying because `c` in Theorem 4.6 may
be composite.  The literal exponent test is

\[
 M_K=c^\nu\quad\Longrightarrow\quad
 \nu\mid\gcd\{\alpha_p(K):p\le x,\,p\ne2,5\}.
\tag{6.8}
\]

In particular, any prime occurring to exponent one forces `nu=1`, which does
not verify the theorem's unspecified sufficiently-large condition.

### 6.1 The reduced denominator cannot be guessed from `Q_K`

Define the exact integer numerator

\[
 A_K=\sum_{n=0}^{K-1}
 16b_n{Q_K\over(2n+1)5^{2n+1}},
 \qquad \pi_K={A_K\over Q_K}.
\tag{6.9}
\]

The integrality follows term by term from (6.2)--(6.5).  Put

\[
 e_K=E_K-\min(E_K,v_5(A_K)),
 \qquad
 m_K={M_K\over(M_K,A_K)}.
\tag{6.10}
\]

Then the reduced denominator of `pi_K` is exactly

\[
 q_K=5^{e_K}m_K,
 \qquad (m_K,10)=1.
\tag{6.11}
\]

For a nonzero moving frequency `h`, its fully reduced denominator is

\[
\boxed{
 q_K(h,j)=
 5^{\max(E_K-v_5(A_Kh)-j,0)}
 {M_K\over(M_K,A_Kh)}.}
\tag{6.12}
\]

Therefore neither `E_K` nor `M_K` may silently be treated as the reduced
parameters.  Conversely, possible cancellation in `A_K` cannot be silently
assumed.  A sufficient package for using the common `e_K`-step split uniformly
over T55/T61 is

\[
\begin{gathered}
 e_K<J,\qquad m_K=c^\nu,\qquad (10,c)=1,
 \qquad \nu\ge\nu_0(10,c),\\
 (h,m_K)<D(10,c)m_K
 \quad\hbox{for every }h\in\mathcal F_{55}\hbox{ or }\mathcal F_{61},
\tag{6.13}
\end{gathered}
\]

followed by (3.7)--(3.9) with `L=J-e_K`.  T55 then requires the aggregate and
transfer inequalities (4.3d) and (7.3a); T61 instead requires
(4.11)--(4.12) and (7.5).  The fully reduced, label-by-label check uses

\[
 \tau_{K,h}=(e_K-v_5(h))_+,
 \qquad M_{K,h}={m_K\over(m_K,h)},
 \qquad L_{K,h}=J-\tau_{K,h}>0,
\tag{6.14}
\]

and repeats every Section 3 hypothesis for `M_(K,h)`.  This can expose an
earlier tail, but it may also change `c`, `nu`, and all source constants from
one adaptive frequency to another.  T63 supplies the exact integer (6.9), but
no theorem proving either the common package (6.13) or the labelwise
valuation, perfect-power, frequency-gcd, and size assertions in (6.14).

## 7. Approximation error is not cancellation

The pinned coefficient estimate `|b_n|<2*5^n` gives, by an absolute tail sum,

\[
 |\pi-\pi_K|\le {8\,5^{-K}\over2K+1}.
\tag{7.1}
\]

Since `|e(x)-e(y)|<=2 pi |x-y|`, for every real `theta`,

\[
 \left|S_J^\pi(h)-S_J^\theta(h)\right|
 \le {2\pi|h|(10^J-1)\over9}|\pi-\theta|.
\tag{7.2}
\]

Thus the T63 certificate proves an error at most `epsilon` only when

\[
\boxed{
 5^K(2K+1)\ge
 {16\pi|h|(10^J-1)\over9\epsilon}.}
\tag{7.3}
\]

This is an approximation inequality; it gives no sign or cancellation for the
rational orbit sum.

Substitution of (7.1) into the exact T55 budget (4.3e) gives

\[
 E_{55}\le {16\pi|C_q|5^{-K}\over2K+1}
 \sum_{u\in\mathcal T_H}\sum_{a=0}^{\nu_{10}(u)}\sum_{j<\ell}
 w_R(u/10^a)
 \left|(u/10^a)10^\ell-u10^j\right|.
\tag{7.3a}
\]

The literal rational-truncation requirement for T55 is therefore (4.3d) with
`E_55` replaced by the right side of (7.3a), in addition to every
Bailey--Crandall hypothesis for every frequency in (4.3).

For the complete T61 variance, the direct endpoint estimate is

\[
 |V(\pi)-V(\pi_K)|
 \le8\pi C_kR^2\ell10^\ell(10^s+1)|\pi-\pi_K|.
\tag{7.4}
\]

To replay (7.4), use
`||z|^2-|z'|^2|<=4|z-z'|` when `|z|,|z'|<=2`, apply the phase Lipschitz bound
to the two endpoints with total multiplier at most
`C_k m_(u,j)(10^s+1)`, and then use `m_(u,j)<R10^ell` and total positive
weight less than `R ell`.  These four factors give the displayed constant
`8 pi C_k R^2 ell 10^ell(10^s+1)`.

Preserving a known strict margin `eta>0` in (4.12) is therefore certified by

\[
\boxed{
 5^K(2K+1)>
 {64\pi C_kR^2\ell10^\ell(10^s+1)\over\eta}.}
\tag{7.5}
\]

There is no known margin `eta` in the pinned sources.

### 7.1 Explicit comparison with the displayed transient

For every `K>=1`,

\[
 2K+1\le5^K.
\tag{7.6}
\]

This follows by induction: it is `3<=5` at `K=1`, and
`2K+3<=5(2K+1)<=5^(K+1)` gives the next case.

For `J>=1`, `h!=0`, and `0<epsilon<=1`, the right side of (7.3) satisfies

\[
 {16\pi|h|(10^J-1)\over9\epsilon}
 \ge16\pi10^{J-1}>5^{J+1}.
\tag{7.7}
\]

The first inequality uses `10^J-1>=9*10^(J-1)`; the last follows from
`16*pi*2^(J-1)>25`.  Combining (7.3), (7.6), and (7.7) gives

\[
 5^{2K}>5^{J+1},\qquad
 E_K\ge2K-1>J.
\tag{7.8}
\]

Hence, when one uses the displayed denominator `Q_K` together with T63's
absolute error certificate at even unit accuracy, its displayed power-of-5
transient consumes the entire length-`J` orbit sum.  For (7.5), replace `eta`
by `min(eta,1)` without losing preservation of the strict margin; its right
side is still larger.  Thus the same direct displayed-denominator comparison
consumes both `J=ell` and `J=s`.

Equation (7.8) is deliberately not asserted for the reduced exponent `e_K`:
that would require a new upper bound for `v_5(A_K)` (and, for each label,
`v_5(h)`).  The exact reduction formula (6.12) records this issue rather than
assuming cancellation in the common numerator.  If such a valuation theorem
shortened the transient, all remaining conditions (6.13), (3.7)--(3.9), the
T55 package (4.3d)/(7.3a), and the T61 package (4.11)--(4.12)/(7.5), or their
labelwise versions (6.14), would still have to be proved.

## 8. Hypothesis-by-hypothesis verdict table

| attempted route | exact post-transient object | result of literal check |
|---|---|---|
| One corrected scalar pi summand | exact modulus `M_(n,h)=m/(m,hb_n)` after transient `tau_(n,d,h)` in (5.10) | no fixed pure-power family, large exponent, uniform gcd constants, or nontrivial T55/T61 bound is supplied |
| Separate bounds for all corrected summands | product identity (5.12) | invalid inference; the exact counterexample (5.13) shows separate cancellation does not control cancellation of the product |
| Displayed common denominator `Q_K` | `5^E_K M_K` from (6.4)--(6.5) | at source-certified precision the displayed transient consumes `J`; `M_K` also requires the literal exponent test (6.8) |
| Reduced common denominator | `5^e_K m_K` from (6.10)--(6.12) | reduction is exactly quantified, but the pinned sources prove none of the valuation, pure-power, sufficiently-large, simultaneous gcd, T55 aggregate, or T61 aggregate requirements in Sections 3, 4, 6, and 7 |
| Uncertified finite sampling | finitely many approximate labeled phases | values alone are not a cancellation theorem and do not certify the strict margins (4.3d) or (4.12) |

Rigorous exact or interval computation can certify one fixed finite strict
inequality.  It does not supply the uniform adaptive-frequency hypotheses or
the analytic cancellation required across the T55/T61 parameter ranges, and
no such certificate is used in this verdict.

The route-specific conclusion is therefore negative in the following precise
sense: the denominator constructions and estimates pinned in T63 do not
verify a Bailey--Crandall tail that is both applicable and nontrivial at the
T55/T61 lengths and adaptive frequency ranges.  This does not prove that no
new theorem can be established about the same rational truncations.  It does
not exclude a different pi-specific representation or unrelated rational
approximants whose **reduced post-transient** denominators satisfy all of
(3.1), (3.7)--(3.9), the T55 package (4.3d)/(7.3a), the T61 package
(4.10)--(4.12)/(7.5), and the required approximation margins.
It has no implication for normality, equidistribution, FSFS, C1, C2, or the
canonical question (1.1).

NO RESCUE FOR T63 DENOMINATORS
