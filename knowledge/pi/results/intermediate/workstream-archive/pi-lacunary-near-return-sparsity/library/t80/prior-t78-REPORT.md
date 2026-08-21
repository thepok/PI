# T78: factorial expansion audit for the fixed pi orbit

Status: `proof sketch`.

Date: 2026-08-07 UTC.

This is one numbered, inspectable audit of the Euler--Li--Rabinowitz--Wagon
factorial expansion. The source audit is `literature-checked` to the extent
recorded in `SOURCE_PINS.md`. The mathematical argument is a `proof sketch`:
it is a rigorous prose proof, not a Lean theorem. It proves no normality,
equidistribution, C1, C2, or canonical near-return upper bound.

## Provenance

- Canonical local source URL: `local:pi-lacunary-near-return-sparsity`.
- Original project source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Delivered byte-exact statement: `canonical_statement.txt`.
- Statement SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Formula sources: Euler (1755), Li E854 (1949), and Rabinowitz--Wagon
  (1995), with URLs, hashes, and exact locators in `SOURCE_PINS.md`.
- Irrationality input: Zeilberger--Zudilin (2020), likewise pinned.
- Prize: none.

## Exact statement

For real `x`, write

\[
 \|x\|_{\mathbb R/\mathbb Z}=\inf_{z\in\mathbb Z}|x-z|.
\]

For integers `n,N >= 1`, the canonical question defines the ordered,
diagonal-inclusive count

\[
 Q_\pi(n,N)=\#\{(i,j):0\le i,j<N,
   \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{0.1}
\]

It asks whether

\[
 \forall A\in\mathbb N_{\ge1}\ \exists n_0\ge1\ \forall n\ge n_0\
 \exists N\ge1:\quad A n Q_\pi(n,N)\le N^2.
\tag{0.2}
\]

## Normalized statement of this audit

For every integer `K>=1`, define

\[
 a_k={2^{k+1}(k!)^2\over(2k+1)!},\qquad
 S_K=\sum_{k=0}^{K-1}a_k={p_K\over q_K},
\tag{0.3}
\]

where `q_K>0` and `gcd(p_K,q_K)=1`, and set `R_K=pi-S_K`.
The audit proves:

1. the infinite sum is exactly `pi`;
2. an exact construction and prime valuation formula for `p_K/q_K`;
3. explicit two-sided tail bounds and a uniform schedule for every literal
   pair `0<=i,j<N`;
4. a two-sided comparison between `Q_pi` and the rational count;
5. the exact transient, order, equality multiplicities, and short-arc count
   for the actual residues of `p_K*10^j modulo q_K`;
6. an occupancy-free short-arc upper bound; and
7. a quantified family-specific obstruction to the recorded
   square-root-modulus rational-orbit scale.

## Ambiguities fixed

- `S_K` contains exactly the terms `0<=k<K`; `a_K` is the first omitted term.
- `p_K/q_K` is reduced. A convenient common denominator is never silently
  treated as the reduced denominator.
- Every pair count is ordered and diagonal-inclusive.
- Every circle inequality is strict, as in the canonical statement.
- The phase transfer is simultaneous for all `0<=i,j<N`, not only one lag.
- The post-transient modulus is the actual reduced cofactor of `q_K`.
- `ord_m(10)` is used only when `gcd(m,10)=1`; for `m=1` its value is defined
  to be one.
- The terminal obstruction concerns absolute-error transfer followed by a
  rational-orbit estimate with square-root-modulus leading cost. It is not a
  denial of every conceivable use of the identity.
- Finite calculations in `verify_note.py` are sanity checks only.

## Known results and search log

| result | source | content used here |
|---|---|---|
| Equivalent double-factorial series | Euler 1755, Ch. I, sec. 11, Ex. II, p. 295 | Primary historical occurrence |
| Exact factorial series and beta proof | Li E854, Monthly 56 (1949), 633--635 | Exact identity and independent comparison |
| Spigot use | Rabinowitz--Wagon 1995, sec. 2 | Exact modern formula and attribution trail |
| `mu(pi)<=7.103205...` | Zeilberger--Zudilin 2020 | Eventual exponent-8 rational lower bound |
| Square-root-modulus orbit estimate | Bailey--Crandall 2002, Thm. 4.6 | Scale used only for the terminal comparison |

Searches were performed on 2026-08-07 through the Euler Archive, Internet
Archive, DOI records, DLMF equation 3.9.6, and the retained project literature
pins. `SOURCE_PINS.md` is the controlling source ledger.

## 1. Independent identity proof

### Proposition 1.1

\[
 \boxed{\displaystyle
 \pi=\sum_{k=0}^{\infty}{2^{k+1}(k!)^2\over(2k+1)!}.}
\tag{1.1}
\]

### Proof

The beta integral at positive integer arguments gives

\[
 { (k!)^2\over(2k+1)!}
 =\int_0^1x^k(1-x)^k\,dx.
\tag{1.2}
\]

On `[0,1]`, `0<=2x(1-x)<=1/2`. Hence the geometric series below converges
uniformly (or, since all terms are nonnegative, Tonelli's theorem applies):

\[
\begin{aligned}
 \sum_{k\ge0}a_k
 &=2\int_0^1\sum_{k\ge0}(2x(1-x))^k\,dx\\
 &=2\int_0^1{dx\over1-2x(1-x)}\\
 &=\int_0^1{dx\over(x-1/2)^2+(1/2)^2}\\
 &=2[\arctan(2x-1)]_0^1=\pi.
\end{aligned}
\tag{1.3}
\]

This proof does not assume any of the cited derivations. It also proves that
every `S_K` is strictly below `pi`. QED.

### Source identity check

Euler prints

\[
 2S=1+{1\over3}+{1\cdot2\over3\cdot5}
 +{1\cdot2\cdot3\over3\cdot5\cdot7}+\cdots,
 \quad S={\pi\over4}.
\tag{1.4}
\]

Since

\[
 (2k+1)!!={(2k+1)!\over2^k k!},
\tag{1.5}
\]

twice Euler's right side has general term

\[
 2{k!\over(2k+1)!!}
 ={2^{k+1}(k!)^2\over(2k+1)!}=a_k.
\tag{1.6}
\]

Thus the pinned primary formula is exactly (1.1), not merely similar to it.

## 2. Exact tail and tail schedule

Retaining the tail of the geometric series in (1.3) gives the exact formula

\[
 \boxed{R_K=2\int_0^1
 {\bigl(2x(1-x)\bigr)^K\over1-2x(1-x)}\,dx.}
\tag{2.1}
\]

Direct cancellation gives

\[
 {a_{k+1}\over a_k}={k+1\over2k+3}<{1\over2}.
\tag{2.2}
\]

Therefore, for every `K>=1`,

\[
 \boxed{a_K<R_K<2a_K.}
\tag{2.3}
\]

Also

\[
 a_K={2^{K+1}\over(2K+1){2K\choose K}}.
\tag{2.4}
\]

The central binomial coefficient is the largest of the `2K+1` coefficients
whose sum is `4^K`; consequently

\[
 {2K\choose K}\ge {4^K\over2K+1}.
\tag{2.5}
\]

Equations (2.3)--(2.5) imply the completely elementary bound

\[
 \boxed{a_K<R_K<2a_K\le2^{2-K}.}
\tag{2.6}
\]

No asymptotic estimate is needed later. For scale interpretation only,
Stirling's formula gives

\[
 a_K\sim{\sqrt\pi\over2^K\sqrt K},\qquad
 R_K\sim{2\sqrt\pi\over2^K\sqrt K}.
\tag{2.7}
\]

The second asymptotic follows by dividing the tail by `a_K`, applying (2.2)
term by term, and using dominated convergence against the geometric series.

## 3. Exact common denominator of the summands

The alternative form

\[
 a_k={2k!\over(2k+1)!!}
\tag{3.1}
\]

shows immediately that every reduced summand denominator is odd. Put

\[
 D_K=\operatorname{lcm}(1,3,5,\ldots,2K-1).
\tag{3.2}
\]

For each odd prime `r`, define

\[
 \alpha_r(K)=\max\{h\ge0:r^h\le2K-1\}.
\tag{3.3}
\]

### Theorem 3.1

The least common denominator of the individual terms
`a_0,...,a_(K-1)` is exactly

\[
 \boxed{D_K=\prod_{\substack{r\le2K-1\\r\ {m odd\ prime}}}
 r^{\alpha_r(K)}.}
\tag{3.4}
\]

### Proof

For an odd prime `r`, Legendre's formula gives the denominator valuation

\[
 d_r(k):=-v_r(a_k)
 =\sum_{h\ge1}\left(
 \left\lfloor{2k+1\over r^h}\right\rfloor
 -2\left\lfloor{k\over r^h}\right\rfloor\right).
\tag{3.5}
\]

Write `k=u r^h+s`, `0<=s<r^h`. The summand in (3.5) is
`floor((2s+1)/r^h)`, hence is zero or one, and is one exactly when
`s>=(r^h-1)/2`. Thus

\[
 \boxed{d_r(k)=\#\{h\ge1:
 k\bmod r^h\ge(r^h-1)/2\}.}
\tag{3.6}
\]

If `k<K`, every contributing `r^h` is at most `2k+1<=2K-1`, so
`d_r(k)<=alpha_r(K)`. Conversely take

\[
 k={r^{\alpha_r(K)}-1\over2}<K.
\tag{3.7}
\]

For every `1<=h<=alpha_r(K)`, reduction modulo `r^h` gives
`k mod r^h=(r^h-1)/2`. Hence all those `h` contribute and
`d_r(k)=alpha_r(K)`. This proves both divisibility by `D_K` and minimality of
every prime exponent. QED.

## 4. Exact reduced partial sums and valuations

Define the explicit integer

\[
 \boxed{P_K=D_KS_K=
 \sum_{k=0}^{K-1}{2k!D_K\over(2k+1)!!}.}
\tag{4.1}
\]

Its integrality follows from Theorem 3.1. Set

\[
 g_K=\gcd(P_K,D_K),\qquad
 p_K={P_K\over g_K},\qquad q_K={D_K\over g_K}.
\tag{4.2}
\]

These equations are an exact reduced expression for the requested partial
sum; in particular they retain every irregular cancellation in `P_K`.

### Theorem 4.1

For every odd prime `r<=2K-1`,

\[
 \boxed{v_r(q_K)=\alpha_r(K)-
 \min(\alpha_r(K),v_r(P_K)).}
\tag{4.3}
\]

For `r=2` or `r>2K-1`, `v_r(q_K)=0`. Equivalently,

\[
 \boxed{q_K=\prod_{\substack{r\le2K-1\\r\ {m odd\ prime}}}
 r^{\alpha_r(K)-\min(\alpha_r(K),v_r(P_K))}.}
\tag{4.4}
\]

### Proof

Equation (4.2) is reduction by the gcd. Taking `r`-adic valuations and using
`v_r(D_K)=alpha_r(K)` proves (4.3). Theorem 3.1 proves that no other primes
occur. QED.

Write the actual reduced denominator as

\[
 q_K=5^{e_K}m_K,\qquad\gcd(m_K,10)=1.
\tag{4.5}
\]

The exact factors are

\[
 e_K=\alpha_5(K)-\min(\alpha_5(K),v_5(P_K)),
\tag{4.6}
\]

and

\[
 m_K=\prod_{\substack{r\le2K-1\\r\ne2,5}}
 r^{\alpha_r(K)-\min(\alpha_r(K),v_r(P_K))}.
\tag{4.7}
\]

In particular,

\[
 \boxed{0\le e_K\le\alpha_5(K),\qquad
 5^{e_K}\le5^{\alpha_5(K)}\le2K-1.}
\tag{4.8}
\]

Thus the power-of-5 transient has length at most logarithmic in `K`. This is
specific to the reduced factorial truncation and does not invoke the
route-specific T65/T68 Zudilin denominator.

## 5. Uniform phase error for every literal pair

For `N>=1`, define

\[
 \varepsilon_{K,N}=(10^{N-1}-1)R_K.
\tag{5.1}
\]

The circle metric is 1-Lipschitz under perturbation of a real representative.
For all `0<=i,j<N`,

\[
\begin{aligned}
 &\left|\|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}
 -\|(10^i-10^j)S_K\|_{\mathbb R/\mathbb Z}\right|\\
 &\qquad\le |10^i-10^j|R_K
 \le(10^{N-1}-1)R_K=\varepsilon_{K,N}.
\end{aligned}
\tag{5.2}
\]

The last bound is sharp enough to avoid the unnecessary factor two obtained
by bounding `10^i+10^j`.

For integers `n,N>=1`, put

\[
 \boxed{K_0(n,N)=2+\left\lceil(N+n)\log_2 10\right\rceil.}
\tag{5.3}
\]

By (2.6),

\[
\begin{aligned}
 \varepsilon_{K_0,N}
 &<(10^{N-1}-1)2^{2-K_0}\\
 &<10^{N-1}10^{-(N+n)}=10^{-(n+1)}.
\end{aligned}
\tag{5.4}
\]

This is the requested explicit tail schedule, simultaneously for every
literal index pair.

## 6. Exact propagation into Q_pi

For `rho>0`, define the rational count

\[
 C_{K,N}(\rho)=\#\{(i,j):0\le i,j<N,
 \|(10^i-10^j)S_K\|_{\mathbb R/\mathbb Z}<\rho\}.
\tag{6.1}
\]

Whenever `0<epsilon_(K,N)<10^(-n)`, (5.2) and the triangle inequality give
the two inclusions

\[
 \boxed{C_{K,N}(10^{-n}-\varepsilon_{K,N})
 \le Q_\pi(n,N)\le
 C_{K,N}(10^{-n}+\varepsilon_{K,N}).}
\tag{6.2}
\]

All inequalities inside the counts remain strict. At the explicit schedule,

\[
 \boxed{C_{K_0,N}(0.9\,10^{-n})
 \le Q_\pi(n,N)\le
 C_{K_0,N}(1.1\,10^{-n}).}
\tag{6.3}
\]

Equation (6.3) is an error transfer only. No rational occupancy assertion has
been inserted into it.

## 7. Actual residues and the power-of-5 transient

Fix `K` and abbreviate

\[
 p=p_K,\quad q=q_K=5^e m,\quad e=e_K,\quad m=m_K.
\tag{7.1}
\]

Because `p/q` is reduced and `q` is odd,

\[
 \gcd(p,m)=1,\qquad\gcd(m,10)=1,
 \qquad e>0\Longrightarrow\gcd(p,5)=1.
\tag{7.2}
\]

For `0<=j<e`, the orbit point is the literal `q`-grid residue

\[
 10^jS_K\equiv{p10^j\bmod q\over q}\pmod1.
\tag{7.3}
\]

For `j=e+t`, exact cancellation gives

\[
 {p10^{e+t}\over5^em}={p2^e10^t\over m}.
\tag{7.4}
\]

Put

\[
 u\equiv p2^e\pmod m.
\tag{7.5}
\]

Then `gcd(u,m)=1`, and the actual post-transient residues are

\[
 \boxed{10^{e+t}S_K\equiv{u10^t\bmod m\over m}\pmod1.}
\tag{7.6}
\]

Define

\[
 \tau_K=\operatorname{ord}_{m_K}(10),
\tag{7.7}
\]

with `tau_K=1` when `m_K=1`.

### Proposition 7.1: exact equality criterion

For `0<=i<j`,

\[
 \boxed{10^iS_K\equiv10^jS_K\pmod1
 \quad\Longleftrightarrow\quad i\ge e_K
 \ \hbox{and}\ \tau_K\mid(j-i).}
\tag{7.8}
\]

### Proof

Reduction of `p/q` makes equality equivalent to

\[
 q\mid10^i(10^{j-i}-1).
\tag{7.9}
\]

The second factor is coprime to both 2 and 5. Hence its product with `10^i`
contains `5^e` exactly when `i>=e`. Once that condition holds, the remaining
condition is `m|10^(j-i)-1`, which is equivalent to the order divisibility in
(7.8). QED.

Consequently all transient points are distinct, no transient point equals a
post-transient point, and the post-transient cycle contains exactly `tau_K`
distinct points.

## 8. Exact collision multiplicities

Put

\[
 e_0=\min(e,N),\qquad L=(N-e)_+.
\tag{8.1}
\]

Write the Euclidean division

\[
 L=A\tau+B,\qquad0\le B<\tau,
\tag{8.2}
\]

where `tau=tau_K`. Among `t=0,...,L-1`, exactly `B` residue classes modulo
`tau` occur `A+1` times and the remaining `tau-B` occur `A` times.

### Theorem 8.1

The exact number of ordered equal rational-orbit pairs is

\[
\boxed{
 E_{K,N}=e_0+(\tau-B)A^2+B(A+1)^2
 =e_0+\tau A^2+2AB+B.}
\tag{8.3}
\]

The first term consists of the transient diagonal. The other terms are the
squares of the post-transient point multiplicities. In particular,
Cauchy--Schwarz (or direct expansion of (8.3)) gives

\[
 \boxed{E_{K,N}\ge e_0+{L^2\over\tau_K}.}
\tag{8.4}
\]

This discharges exact collision multiplicity rather than assuming that the
cycle is injective beyond its proved period.

## 9. Exact short-arc occupancy

For `0<=r<tau`, let

\[
 y_r=u10^r\bmod m,
\tag{9.1}
\]

and define the exact occurrence weights

\[
 w_r=\begin{cases}
 A+1,&0\le r<B,\\
 A,&B\le r<\tau.
 \end{cases}
\tag{9.2}
\]

For every `0<rho<=1/2`, direct partition of both indices into transient and
cycle parts gives the complete formula

\[
\boxed{\begin{aligned}
C_{K,N}(\rho)={}&
\sum_{0\le i,j<e_0}
 {\bf1}\!\left(\left\|{p(10^i-10^j)\over q}\right\|<\rho\right)\\
&+2\sum_{i<e_0}\sum_{r<\tau}w_r
 {\bf1}\!\left(\left\|{p10^i\over q}-{y_r\over m}\right\|<\rho\right)\\
&+\sum_{r,s<\tau}w_rw_s
 {\bf1}\!\left(\left\|{y_r-y_s\over m}\right\|<\rho\right).
\end{aligned}}
\tag{9.3}
\]

Thus the requested short-arc occupancy is explicit in the actual numerator,
reduced denominator, multiplicative order, and strict threshold. Formula
(9.3) is finite and exact; it is not an unnamed occupancy hypothesis.

There is also a uniform occupancy-free upper bound. For odd `M`, define

\[
 H_M(\rho)=\min\left({M-1\over2},\lceil\rho M\rceil-1\right).
\tag{9.4}
\]

Exactly `2H_M(rho)+1` points of the full `M`-grid have strict circle distance
less than `rho` from a fixed `M`-grid point. An arbitrary open arc of length
`2rho` contains at most `ceil(2rho M)` full-grid points. Finally set

\[
 \mu=\max(1,\lceil L/\tau\rceil).
\tag{9.5}
\]

Every occupied cycle point has multiplicity at most `mu`. Applying the two
full-grid facts separately to the three lines of (9.3) proves

\[
\boxed{\begin{aligned}
C_{K,N}(\rho)\le{}&
e_0\min(e_0,2H_q(\rho)+1)\\
&+2e_0\mu\min(\tau,\lceil2\rho m\rceil)\\
&+L\mu\min(\tau,2H_m(\rho)+1).
\end{aligned}}
\tag{9.6}
\]

This estimate can be trivial when `rho*m` is large, but that behavior is an
explicit inequality, not an unresolved occupancy placeholder.

## 10. Exact order obstruction to a canonical witness

Assume `epsilon_(K,N)<10^(-n)`. Every exact rational collision counted by
`E_(K,N)` then satisfies

\[
 \|(10^i-10^j)\pi\|
 \le |10^i-10^j|R_K\le\varepsilon_{K,N}<10^{-n}.
\tag{10.1}
\]

Therefore

\[
 \boxed{Q_\pi(n,N)\ge E_{K,N}
 \ge e_0+{L^2\over\tau_K}.}
\tag{10.2}
\]

If this same `N` were a canonical witness for a given `A,n`, then
`AnQ_pi<=N^2` would force the necessary condition

\[
 \boxed{\tau_K\ge An\left({L\over N}\right)^2.}
\tag{10.3}
\]

Thus small actual order is a proved obstruction. The terminal verdict below
does not assume that the order is small.

## 11. Irrationality input and reduced-modulus lower bound

The pinned Zeilberger--Zudilin source defines `mu(pi)` as the least exponent
such that, for every positive `eta`, all integers `p` and all sufficiently
large positive denominators `q` satisfy

\[
 \left|\pi-{p\over q}\right|>q^{-(\mu(\pi)+\eta)}.
\tag{11.1}
\]

It proves

\[
 \mu(\pi)\le7.10320533413700172750577342281\ldots<{36\over5}.
\tag{11.2}
\]

Take `eta=4/5` in the definition. Then
`mu(pi)+eta<36/5+4/5=8`, so for every `q>=1`,
`q^(-(mu(pi)+eta))>=q^(-8)`. This gives the exact quantified consequence

\[
 \boxed{\exists Q_8\ge1\ \forall q\ge Q_8\ \forall p\in\mathbb Z:
 \left|\pi-{p\over q}\right|>q^{-8}.}
\tag{11.3}
\]

The source supplies no numerical value for `Q_8`, and none is claimed here.

The strictly increasing rational sequence `S_K` converges to the irrational
number `pi`. Hence `q_K` tends to infinity: otherwise infinitely many `S_K`
would lie in the finite set of reduced rationals in `[2,4]` with denominator
bounded by one fixed integer. Consequently there exists `K_8` such that
`q_K>=Q_8` for every `K>=K_8`.

### Theorem 11.1

For every `K>=K_8`,

\[
 \boxed{q_K>2^{(K-2)/8},\qquad
 m_K>{2^{(K-2)/8}\over2K-1},\qquad
 \sqrt{m_K}>{2^{(K-2)/16}\over\sqrt{2K-1}}.}
\tag{11.4}
\]

### Proof

Apply (11.3) to `p_K/q_K`, then use (2.6):

\[
 q_K^{-8}<\left|\pi-{p_K\over q_K}\right|
 =R_K<2^{2-K}.
\tag{11.5}
\]

This gives the first inequality of (11.4). Equations (4.5) and (4.8) give
`q_K=5^(e_K)m_K<=(2K-1)m_K`, proving the second. Taking square roots proves
the third. QED.

## 12. Terminal family-specific scale obstruction

We first record what the convenient schedule implies, and then remove the
choice of schedule. Let `n,N>=1`, set

\[
 M=N+n,\qquad K=K_0(n,N).
\tag{12.1}
\]

The uniform transfer schedule (5.3) gives

\[
 2^{K-2}\ge10^{N+n}=10^M.
\tag{12.2}
\]

If `K>=K_8`, Theorem 11.1 therefore yields the displayed pi-specific bound

\[
 \boxed{\sqrt{m_K}>{10^{M/16}\over\sqrt{2K-1}}.}
\tag{12.3}
\]

This can be made literal without asymptotic notation. Since
`log_2(10)<4`,

\[
 K=2+\lceil M\log_2 10\rceil\le4M+2,
 \quad 2K-1\le8M+3\le11M.
\tag{12.4}
\]

For every integer `M>=100`,

\[
 10^{M/16}>\sqrt{11}\,M^{3/2}.
\tag{12.5}
\]

For completeness, at `M=100` the left side exceeds `10^6`, while the right
side is below `4*1000`. The logarithmic derivative of
`10^(x/16)/x^(3/2)` is `log(10)/16-3/(2x)>0` for `x>=100` (use
`log(10)>2`), so the inequality persists.

Combining (12.3)--(12.5), for every `n,N>=1` satisfying

\[
 N+n\ge100\quad\hbox{and}\quad K_0(n,N)\ge K_8,
\tag{12.6}
\]

one has

\[
 \boxed{\sqrt{m_{K_0(n,N)}}>N\ge L.}
\tag{12.7}
\]

If `L=0`, there is no post-transient rational orbit to estimate. If `L>0`,
(12.7) says that even the bare optimistic square-root-modulus cost is larger
than the entire post-transient sum length at this convenient schedule.

The convenient schedule is not by itself a family-wide obstruction. We now
prove the needed statement for every truncation that is accurate enough for
absolute-error transfer.

Assume `N>=2`, put `M=N+n`, and let `K>=1` satisfy the literal transfer
condition

\[
 \varepsilon_{K,N}=(10^{N-1}-1)R_K<10^{-n}.
\tag{12.8}
\]

The lower tail bound in (2.3), the identity (2.4), and the elementary upper
bound `{2K choose K}<=4^K` give

\[
 R_K>a_K\ge {2^{1-K}\over2K+1}.
\tag{12.9}
\]

Because `N>=2`,

\[
 10^{N-1}-1\ge9\,10^{N-2}.
\tag{12.10}
\]

Combining (12.8)--(12.10) yields the necessary truncation-depth inequality

\[
 \boxed{2^{K-1}(2K+1)>9\,10^{M-2}.}
\tag{12.11}
\]

Let `Kbar=K_0(n,N)`. For `K>=13`, the function

\[
 F(K)={2^{(K-2)/16}\over\sqrt{2K-1}}
\tag{12.12}
\]

is increasing: the logarithmic derivative of its real extension is
`log(2)/16-1/(2K-1)>0`, using `log(2)>2/3` and `K>=13`.

There are two cases. If `K>=Kbar`, monotonicity and (12.2) give

\[
 F(K)\ge F(Kbar)\ge {10^{M/16}\over\sqrt{2Kbar-1}}.
\tag{12.13}
\]

If `K<Kbar`, (12.11) gives

\[
 F(K)>
 {\left(9\,10^{M-2}/(2(2Kbar+1))\right)^{1/16}
  \over\sqrt{2Kbar-1}}.
\tag{12.14}
\]

Using `Kbar<=4M+2`, both cases imply the common lower bound

\[
 \boxed{F(K)>
 {\left(9\,10^{M-2}/(26M)\right)^{1/16}\over\sqrt{11M}}.}
\tag{12.15}
\]

The right side divided by `M` tends to infinity, since it is

\[
 { (9/26)^{1/16}10^{(M-2)/16}
  \over\sqrt{11}\,M^{25/16}}.
\tag{12.16}
\]

This is also an explicit eventual comparison. For `M=200`, its numerator is
greater than `(1/2)10^12`, while its denominator is less than
`4*200^2<2*10^5`; and its logarithmic derivative is
`log(10)/16-25/(16M)>0` for `M>=200`. Thus (12.16) is greater than one for
every `M>=200`.

The irrationality threshold introduces only one further eventual constant.
Choose `M_8` so large that

\[
 9\,10^{M_8-2}>2^{K_8-1}(2K_8+1).
\tag{12.17}
\]

Then (12.11) forces `K>=K_8` whenever `M>=M_8`. Enlarging `M_8` to at least
`200` also forces `K>=13`. Theorem 11.1 and (12.15)--(12.16) now prove the
literal family-wide statement

\[
\boxed{\begin{gathered}
 \exists M_*\ge200\ \forall n\ge1\ \forall N\ge2\ \forall K\ge1,\\
 N+n\ge M_*\ \wedge\ \varepsilon_{K,N}<10^{-n}
 \quad\Longrightarrow\quad
 \sqrt{m_K}>N\ge(N-e_K)_+.
\end{gathered}}
\tag{12.18}
\]

For `N=1`, the transfer error is identically zero, so no lower bound on `K`
is possible or needed. The canonical count is exactly `Q_pi(n,1)=1`, and
`AnQ_pi(n,1)<=1` fails whenever `An>1`. Thus the degenerate one-point orbit
cannot be a canonical witness at the eventual depths under discussion.

Bailey--Crandall Theorem 4.6, pinned in `SOURCE_PINS.md`, has the
source-faithful majorant

\[
 B\left(A\sqrt m+{L\over\sqrt m}\right)\log m.
\tag{12.18a}
\]

Its positive constants may be enlarged, without weakening the theorem, so
that `A,B>=1`. Under (12.18), `N>=2` and `sqrt(m)>N` imply `m>4` and hence
`log(m)>1`. Therefore the displayed majorant is strictly larger than
`sqrt(m)>N>=L`. Even granting every otherwise missing pure-power, fixed-base,
large-exponent, and frequency-gcd hypothesis, this recorded estimate cannot
certify a nontrivial length-`L` bound. If the base varies with `K`, the source
supplies no uniform constants in the first place.

The terminal verdict is therefore:

\[
\boxed{\begin{minipage}{0.91\linewidth}
The Euler--Li factorial truncation has an exact and short power-of-5
transient. For every truncation `K` whose absolute error is small enough
uniformly over all `0<=i,j<N`, the proven irrationality measure and the exact
tail lower bound force the actual reduced post-transient cofactor to satisfy
`sqrt(m_K)>N`, with the literal quantifiers in (12.18). Thus this family cannot
improve the recorded square-root-modulus rational-approximation scale through
absolute-error transfer. This obstruction is independent of any unproved
short-arc occupancy estimate.
\end{minipage}}
\tag{12.19}
\]

This is family- and route-specific. It does not rule out an argument that
uses cancellation in the truncation error before absolute values, an orbit
estimate with no positive square-root-modulus cost, or unrelated
approximations to `pi`.

## 13. Relation to T7 and the canonical question

The machine-checked T7 interface identifies finite decimal-cylinder collision
energy as an exact canonical frontier and compares it with `Q_pi` up to a
factor three. This audit does not instantiate T7: (9.6) is generally too large
when `rho*m_K` is large, and (12.9) proves that the recorded square-root route
cannot repair that at the available orbit length.

No claim in this note is that T65, T68, or any sketch proves the present
obstruction. T65 is an unverified note about a different Zudilin expansion.
T68 is machine-checked but denies only its own displayed-denominator package.
Sections 1--12 above independently analyze this factorial family.

## 14. Experiments and replay

`verify_note.py` performs exact-rational sanity checks for bounded `K,N`:

- exact common and reduced denominators;
- the prime valuation formula;
- the power-of-5 transient bound;
- the equality criterion and multiplicity formula; and
- the complete short-arc formula against direct enumeration.

It also verifies all delivered source hashes and source-text anchors. Run it
inside a directory containing only the delivered artifacts:

```text
python verify_note.py
```

The finite computations are labeled `sanity checks`; they are not evidence
for any universal statement. Every universal assertion used in the verdict
has a displayed proof above.

## 15. Formalization map and independent review

- Lean statement: none in this note item.
- Existing machine-checked interface consulted: T7's exact canonical finite
  frontier; it is not used as a premise of the negative endpoint.
- Reusable future lemmas: Theorems 3.1, 4.1, 8.1, the exact formula (9.3),
  and Theorem 11.1.
- Main theorem and axiom audit: not applicable; status remains `proof sketch`.
- Statement checked by: pending independent skeptic.
- Proof checked by: pending independent skeptic.
- Novelty/attribution checked by: source trail pinned; expert review pending.

## 16. Non-claims

- No canonical witness `N` is produced.
- No upper bound sufficient for C1 or C2 is proved.
- No normality, equidistribution, digit independence, or local pi-digits
  assertion is made.
- No finite calculation is promoted to proof.
- No unknown occupancy estimate is an endpoint: (9.3) is exact, (9.6) is an
  unconditional upper bound, and the final obstruction (12.9) bypasses
  occupancy entirely.
