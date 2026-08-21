# T15: proof of the exact scale-matched L1 tail

Status: `proof sketch` (complete rigorous prose proof, not machine-checked).

## 1. Claim boundary and source pins

The immutable canonical source is the local file
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`. It has no external
source URL: the problem was formulated locally by this theory program on
2026-07-23. Its SHA-256 was checked before this note was written:

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That canonical question concerns the fixed decimal expansion of pi and the
ordered collision count `R_pi(m,N)`. This note does not address that question.
It proves only the Lebesgue-almost-everywhere phase sibling obtained by
replacing T8's orbit value by a variable `alpha in [0,1)`. The `pi` in
`exp(2*pi*i*x)` remains the universal circle constant.

The deterministic definitions used below come from the machine-checked T8
module
`TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction`, whose
staged source has SHA-256

```text
f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9
```

The T14 note has status `proof sketch`. It is used only as motivation and as
the source of the exact displayed statement `Tail(t)` attacked here. No claim
asserted only in T14 is treated as a premise. Every finite identity needed for
the proof is rederived below.

## 2. Normalized statement and quantifiers

For positive integers `m,N`, set

\[
 H=H_m=10^m,\qquad
 T_t(m,N)=N+N^2H^{-t}=N(1+NH^{-t}).                 \tag{2.1}
\]

Define the ordered restricted domain

\[
 Q_{m,N}=\{(a,b)\in\mathbb Z^2:0\le a,b<N,
                         |a-b|\ge m\},              \tag{2.2}
\]

and, for `q=(a,b)`,

\[
 \lambda_q=10^a-10^b,\qquad e(x)=\exp(2\mathop{\rm pi}ix). \tag{2.3}
\]

For every inclusive positive frequency `1<=h<=H`, put

\[
 S_h(\alpha;m,N)=\sum_{q\in Q_{m,N}}e(h\lambda_q\alpha),
 \qquad
 A(\alpha;m,N)=\sum_{h=1}^{H}|S_h(\alpha;m,N)|.       \tag{2.4}
\]

The exact statement to be proved is:

**Tail(t).** For every rational `t` with `0<t<1`, there exist constants

\[
 K_t\ge1,\qquad C_t>0,\qquad p_t>1,                   \tag{2.5}
\]

chosen before `m,N`, such that all positive integers `m,N` satisfy

\[
 \operatorname{Leb}\{\alpha\in[0,1):
 A(\alpha;m,N)>K_tH T_t(m,N)\}
 \le {C_t\over H(1+NH^{-t})^{p_t}}.                  \tag{2.6}
\]

We will prove the stronger statement that (2.6) holds for every real
`0<t<1`, with constants independent even of `t`:

\[
 \boxed{K_t=2,\qquad C_t=127758496,\qquad p_t=4.}     \tag{2.7}
\]

The conventions and formerly ambiguous quantifiers are therefore fixed as
follows.

1. Pairs are ordered, and both orientations occur.
2. The lag condition is the weak inequality `m<=|a-b|<=N-1`.
3. Frequencies are exactly `1,...,10^m`, including both endpoints.
4. Lebesgue measure is on `[0,1)`; every function is one-periodic.
5. An upper summation endpoint below its lower endpoint gives an empty sum.
6. None of `K_t,C_t,p_t` depends on `m,N`.

## 3. Recovery of T8's exact domain

T8 represents a pair by an orientation and a core `(r,n)` satisfying

\[
 0<r,\qquad m\le r<N,\qquad 0\le n<N-r,               \tag{3.1}
\]

unless `ArithmeticExcluded(8,1,Q0,m,n,r)` holds. Its structured denominator
is

\[
 d(n,r)=10^n(10^r-1),                                  \tag{3.2}
\]

and the exclusion at `(mu,c)=(8,1)` is

\[
 Q_0\le d(n,r)\quad\hbox{and}\quad10^{-m}\le d(n,r)^{-7}.
                                                               \tag{3.3}
\]

For every core in (3.1), put `x=10^m-1`. Then

\[
 d(n,r)\ge10^m-1=x\ge9.                               \tag{3.4}
\]

Moreover, `x^7>x^2>x+1=10^m`, because
`x^2-(x+1)=x(x-1)-1>=71`. Hence

\[
 d(n,r)^{-7}<10^{-m}.                                  \tag{3.5}
\]

The second conjunct of (3.3) is false, independently of `Q0`. Thus T8's
exclusion is empty here. Its two orientations map `(r,n)` to `(n+r,n)` and
`(n,n+r)`. Conversely, every pair in (2.2) has the unique core

\[
 n=\min(a,b),\qquad r=|a-b|,                            \tag{3.6}
\]

and its order determines the orientation. This is a bijection with (2.2).

Put `L=(N-m)_+=max(N-m,0)`. If `N<=m`, the domain is empty. If `N>m`, each
lag `r=m,...,N-1` has `N-r` starts and two orientations. Therefore, for every
positive `m,N`,

\[
 \boxed{|Q_{m,N}|=2\sum_{r=m}^{N-1}(N-r)=L(L+1)\le N^2.} \tag{3.7}
\]

## 4. Frequency injectivity and finite moments

Every member has the unique oriented form

\[
 \lambda_{\sigma,r,n}=\sigma10^n(10^r-1),              \tag{4.1}
\]

where `sigma` is `+1` or `-1`, `m<=r<N`, and `0<=n<N-r`.
The sign recovers `sigma`; the exact number of trailing decimal zeroes
recovers `n`; division by `10^n` then recovers `r`. Hence

\[
 q\longmapsto\lambda_q\quad\hbox{is injective on }Q_{m,N}. \tag{4.2}
\]

For every integer `z`, direct integration gives

\[
 \int_0^1e(z\alpha)\,d\alpha={\bf1}_{z=0}.             \tag{4.3}
\]

All sums are finite, so expansion and termwise integration are valid. For
every `1<=h<=H`, (4.2)-(4.3) give

\[
 \int_0^1S_h\,d\alpha=0,\qquad
 \int_0^1|S_h|^2\,d\alpha=|Q_{m,N}|.                  \tag{4.4}
\]

The reverse of `q` has frequency `-lambda_q`, so `S_h` is real. Define

\[
 E(\alpha;m,N)=\sum_{h=1}^{H}|S_h(\alpha;m,N)|^2.       \tag{4.5}
\]

Summing (4.4), and applying pointwise Cauchy-Schwarz, proves

\[
 \boxed{\int_0^1E\,d\alpha=H|Q_{m,N}|,\qquad
        E\le A^2\le HE.}                              \tag{4.6}
\]

## 5. Complete cross-frequency classification

This section classifies every relation

\[
 h\lambda_{\sigma,r,n}=k\lambda_{\tau,s,d},
 \qquad1\le h,k\le H.                                  \tag{5.1}
\]

For a positive integer `j`, define

\[
 v_{10}(j)=\max\{u\ge0:10^u\mid j\},\qquad
 j^\circ=j/10^{v_{10}(j)}.                             \tag{5.2}
\]

The primitive part `j^circ` is not divisible by 10, although it may still be
divisible by 2 or by 5. In the inclusive legal range,
`0<=v_10(j)<=m`; valuation `m` occurs only for `j=H`, with primitive part 1.
Write

\[
 h=10^u h^\circ,\qquad k=10^v k^\circ.                 \tag{5.3}
\]

Positivity in (5.1) first forces `sigma=tau`. Comparing exact powers of 10
and then canceling them gives

\[
 n+u=d+v,\qquad
 h^\circ(10^r-1)=k^\circ(10^s-1).                     \tag{5.4}
\]

Let `g=gcd(r,s)`. If `r>=s`, reduction modulo `10^s-1` gives

\[
 10^r-1\equiv10^{r\bmod s}-1\pmod{10^s-1}.
\]

Iterating the ordinary Euclidean algorithm on `(r,s)` therefore reduces the
integer gcd to `10^g-1`; conversely, `g` divides both exponents, so `10^g-1`
divides both repunits. Hence

\[
 \gcd(10^r-1,10^s-1)=10^g-1.                          \tag{5.5}
\]

If `r>s`, equation (5.4) forces

\[
 {10^r-1\over10^g-1}\mid k^\circ.                     \tag{5.6}
\]

Because `g` divides `r-s`, one has `g<=r-s` and `r-g>=s>=m`. But

\[
 {10^r-1\over10^g-1}=1+10^g+\cdots+10^{r-g}
 >10^{r-g}\ge10^m=H,                                  \tag{5.7}
\]

contrary to `k^circ<=k<=H`. The case `s>r` is symmetric. Thus `r=s`,
and (5.4) then gives `h^circ=k^circ`. We have proved the exact equivalence

\[
 \boxed{
 h\lambda_{\sigma,r,n}=k\lambda_{\tau,s,d}
 \Longleftrightarrow
 \begin{cases}
 \sigma=\tau,\\
 r=s,\\
 h^\circ=k^\circ,\\
 n+v_{10}(h)=d+v_{10}(k).
 \end{cases}}                                          \tag{5.8}
\]

Thus opposite orientations, distinct lags, and distinct primitive frequency
chains never collide. Every collision belongs to one chain

\[
 j,10j,10^2j,\ldots,\qquad10\nmid j.                  \tag{5.9}
\]

For fixed `h,k`, let

\[
 \delta=|v_{10}(h)-v_{10}(k)|,\qquad
 D=(L-\delta)_+.                                       \tag{5.10}
\]

At lag `r`, the last equation in (5.8) has `(N-r-delta)_+` start pairs for
each orientation. Summing gives the exact covariance

\[
 \boxed{
 \int_0^1S_h\overline{S_k}\,d\alpha=
 \begin{cases}
 D(D+1),&h^\circ=k^\circ,\\
 0,&h^\circ\ne k^\circ.
 \end{cases}}                                          \tag{5.11}
\]

For every `1<=delta<=m`, the inclusive frequency range contains exactly
`2*10^(m-delta)` ordered pairs `(h,k)` with common primitive part and
valuation distance `delta`; the endpoint `h=H` is included in this count.
There are none for `delta>m`. Consequently

\[
 \sum_{h,k=1}^{H}\int_0^1S_h\overline{S_k}\,d\alpha
 =HL(L+1)+2\sum_{\delta=1}^{\min(m,L-1)}10^{m-\delta}
  (L-\delta)(L-\delta+1).                              \tag{5.12}
\]

This audits all cross-frequency 10-adic cases. The proof below does not
incorrectly treat the `S_h` as independent.

## 6. Exact energy variance

For `d>0`, define the ordered multiplicity

\[
 M(d)=|\{(q,q')\in Q_{m,N}^2:
              \lambda_q-\lambda_{q'}=d\}|.             \tag{6.1}
\]

Injectivity makes `q!=q'` automatic when `d>0`. Swapping `q,q'` shows that
the multiplicity at `-d` is also `M(d)`. Expanding (4.5) gives

\[
 E-H|Q|=\sum_{h=1}^{H}\sum_{d>0}M(d)
          \bigl(e(hd\alpha)+e(-hd\alpha)\bigr).         \tag{6.2}
\]

The positive Fourier coefficient at `z>0` is therefore

\[
 c_z=\sum_{\substack{h\mid z\\1\le h\le H}}M(z/h).    \tag{6.3}
\]

Parseval gives

\[
 \operatorname{Var}(E)=2\sum_{z>0}c_z^2.               \tag{6.4}
\]

For fixed `d,e>0`, the equality `hd=ke` can be solved exactly. Write
`d=g d_0`, `e=g e_0`, where `g=gcd(d,e)` and `gcd(d_0,e_0)=1`. Its positive
solutions are

\[
 h=e_0\ell,\qquad k=d_0\ell,
 \qquad1\le\ell\le {H g\over\max(d,e)}.               \tag{6.5}
\]

Thus

\[
 \boxed{
 \operatorname{Var}(E)=
 2\sum_{d,e>0}M(d)M(e)
 \left\lfloor{H\gcd(d,e)\over\max(d,e)}\right\rfloor.} \tag{6.6}
\]

It remains to prove one finite weighted-GCD estimate, without assuming any
false additivity of `v_10` under multiplication.

## 7. Signed decimal vectors and all valuation cases

Every occurrence counted by `M(d)` has the form

\[
 d=10^a+10^f-10^b-10^c.                               \tag{7.1}
\]

Its combined signed decimal coefficients lie in `[-2,2]`. If two different
coefficient vectors represented the same integer, their difference would
have coefficients in `[-4,4]`. At its largest nonzero exponent `R`, the
leading term has magnitude at least `10^R`, whereas all lower terms have
total magnitude at most

\[
 4\sum_{j<R}10^j={4(10^R-1)\over9}<10^R.              \tag{7.2}
\]

This is impossible. Hence the signed decimal vector is uniquely determined
by `d`; denote its finitely supported coefficients by `c_j(d)`.

Treat `a,f` as two labeled positive tokens and `b,c` as two labeled negative
tokens. Opposite-sign cancellation lowers `sum_j |c_j(d)|` by 2, while
combining same-sign tokens does not change that sum. Define

\[
 C=\{d>0:M(d)>0,\ \sum_j|c_j(d)|=2\},\qquad
 P=\{d>0:M(d)>0,\ \sum_j|c_j(d)|=4\}.                 \tag{7.3}
\]

A nonzero vector has exactly one of the following forms.

1. **Cancellation sector `C`.** Every representation contains one hidden
   opposite-sign token pair, leaving `d=10^u-10^v` for unique `u>v`.
2. **Primitive four-token sector `P`.** No exponent carries tokens of
   opposite signs.

Two canceled pairs would give `d=0`, so signed-vector uniqueness makes this
split exhaustive and disjoint.
In the primitive sector, assigning the two positive and two negative tokens
to their labels gives

\[
 \boxed{M(p)\le2!2!=4\qquad(p\in P).}                  \tag{7.4}
\]

In the cancellation sector, let `z` be the hidden canceled exponent. The only
potentially legal labeled representations of `10^u-10^v` are

\[
 (q,q')=((a,b),(c,f))
 =((u,z),(v,z))\quad\hbox{or}\quad((z,v),(z,u)).       \tag{7.5}
\]

The other two labelings make one ordered pair diagonal. Therefore

\[
 M(10^u-10^v)=
 2|\{z:0\le z<N,\ |u-z|\ge m,\ |v-z|\ge m\}|\le2N.   \tag{7.6}
\]

There are fewer than `N^2/2` cancellation values, so

\[
 \sum_{c\in C}M(c)<N^3.                               \tag{7.7}
\]

Every unordered pair of distinct elements of `Q` contributes once to exactly
one positive difference. Using (3.7) and injectivity,

\[
 \sum_{d>0}M(d)=\binom{|Q|}{2}<N^4/2,
 \qquad\sum_{p\in P}M(p)<N^4/2.                       \tag{7.8}
\]

For a noncancelling signed vector `x`, let `ell(x)` be its lowest nonzero
decimal exponent. The coefficient there is `c in {+1,-1,+2,-2}`, so

\[
 x=10^{\ell(x)}(c+10A)                                \tag{7.9}
\]

for an integer `A`. Since `5` does not divide `c`,

\[
 v_5(x)=\ell(x),\qquad v_{10}(x)=\ell(x).              \tag{7.10}
\]

If `c` is odd then `v_2(x)=ell(x)`. If `c=+2` or `-2`, the additional
2-adic valuation of `c+10A` is not fixed and must remain part of the primitive
factor. This is the complete safe 10-adic split; in particular, we make no
false inference from `v_10` alone about an ordinary gcd. For cancellation
values

\[
 D_{v,r}=10^v(10^r-1),                                 \tag{7.11}
\]

one has exactly `v_2(D)=v_5(D)=v_10(D)=v`.

The next lemma controls the complete reduced ratio and therefore retains all
remaining 2-adic, 5-adic, odd, and cyclotomic common factors.

## 8. Sparse-decimal rational-neighbor lemma

Call

\[
 x=\sum_{i=1}^{s}\varepsilon_i10^{a_i}                \tag{8.1}
\]

a noncancelling `s`-token form if every `a_i` is a nonnegative integer,
`epsilon_i` is `+1` or `-1`, and no exponent occurs with both signs.
Repetitions with the same sign are allowed.
Cancellation values use the prescribed sign pattern `(+,-)` with `s=2`;
primitive values use `(+,+,-,-)` with `s=4`.

For positive `x,y`, define the reduced-ratio height

\[
 \mathcal H(x,y)={\max(x,y)\over\gcd(x,y)}.            \tag{8.2}
\]

**Lemma 8.1.** Let `x` and `y` be positive noncancelling `s`- and `u`-token
forms, respectively, with prescribed signs, nonnegative integer exponents,
and `1<=s,u<=4`. Suppose
`mathcal H(x,y)<=K`, where `K>=1`. If the positive integer `J` satisfies

\[
 10^J>(s+u)K,                                          \tag{8.3}
\]

then every exponent of `y` lies within

\[
 (s+u-1)(J-1)                                          \tag{8.4}
\]

of an exponent of `x`. Consequently, for fixed `x`, the number of possible
labeled exponent vectors for `y` is at most

\[
 \boxed{\left[s\bigl(2(s+u-1)(J-1)+1\bigr)\right]^u.} \tag{8.5}
\]

**Proof.** Put `g=gcd(x,y)`, `h=y/g`, and `k=x/g`. Then

\[
 hx=ky,\qquad \gcd(h,k)=1,
 \qquad\max(h,k)=\mathcal H(x,y)\le K.                 \tag{8.6}
\]

After moving one side to the other, (8.6) is a zero sum of `s+u` labeled
terms of the form `+/- h*10^a` or `+/- k*10^b`, each with coefficient
magnitude at most `K`.

Make a graph on these token occurrences, joining two whenever their exponents
differ by less than `J`. Consider the component with the largest exponents,
and let `r` be its smallest exponent. If its sum were nonzero, that integer
would be divisible by `10^r`, so its magnitude would be at least `10^r`.
Every token in a lower component has exponent at most `r-J`; hence all lower
components together have magnitude at most

\[
 (s+u)K10^{r-J}<10^r                                  \tag{8.7}
\]

by (8.3). They cannot cancel the highest component. Therefore the highest
component has sum zero. Removing it and repeating downward shows that every
component has sum zero.

No nonempty subset of the tokens of a noncancelling form with at most four
tokens can sum to zero. Indeed, at the subset's highest exponent `R`, all
tokens have the same sign and contribute magnitude at least `10^R`. If
`R=0`, there are no lower exponents. If `R>=1`, at most three lower tokens
contribute at most `3*10^(R-1)<10^R`. A component containing only `x`-tokens
would be `h` times such a nonzero token-subsum, and one containing only
`y`-tokens would be `-k` times one. Thus every component containing a
`y`-token must also contain an `x`-token.

A simple path from that `y`-token to an `x`-token uses at most `s+u-1` edges,
each changing the exponent by at most `J-1`. This proves (8.4). The possible
exponents of each labeled `y`-token therefore lie in the union of `s` integer
intervals, each of length at most `2(s+u-1)(J-1)+1`. Choosing all `u` labeled
exponents proves (8.5). QED.

## 9. Primitive weighted-GCD sectors

Distinct positive integers have integer reduced-ratio height at least 2.
Partition them into the disjoint shells

\[
 10^j<\mathcal H(x,y)\le10^{j+1},\qquad j=0,1,2,\ldots. \tag{9.1}
\]

Apply Lemma 8.1 with `K=10^(j+1)` and `J=j+2`. Since `s+u<=8`,

\[
 10^J=10K>8K\ge(s+u)K.                                \tag{9.2}
\]

For primitive-to-primitive neighbors, `s=u=4`. Through the end of shell `j`,
the number of possible primitive vectors is at most

\[
 \bigl(4(14(J-1)+1)\bigr)^4
 \le(56(j+2))^4.                                      \tag{9.3}
\]

For cancellation-to-primitive neighbors, `s=2,u=4`, and the corresponding
bound is

\[
 \bigl(2(10(J-1)+1)\bigr)^4
 \le(20(j+2))^4.                                      \tag{9.4}
\]

The cumulative count may overcount a shell, which is harmless. For
`|x|<1`, repeated differentiation of the geometric series gives

\[
 \begin{aligned}
 \sum_{j\ge0}jx^j&={x\over(1-x)^2},\\
 \sum_{j\ge0}j^2x^j&={x(1+x)\over(1-x)^3},\\
 \sum_{j\ge0}j^3x^j&={x(1+4x+x^2)\over(1-x)^4},\\
 \sum_{j\ge0}j^4x^j&={x(1+11x+11x^2+x^3)\over(1-x)^5}.
 \end{aligned}                                        \tag{9.5}
\]

Substitute `x=1/10` and
`(j+2)^4=j^4+8j^3+24j^2+32j+16`. This gives

\[
 \mathcal S_4:=\sum_{j=0}^{\infty}{(j+2)^4\over10^j}
 ={540170\over19683}.                                  \tag{9.6}
\]

Fix `p in P`. Its diagonal neighbor contributes at most `M(p)<=4`. For every
other primitive neighbor in shell `j`, the kernel is at most `10^(-j)` and
its multiplicity is at most 4. Thus

\[
 \sum_{p'\in P}M(p'){
 \gcd(p,p')\over\max(p,p')}
 \le4+4\,56^4\mathcal S_4
 ={21249198896012\over19683}=:A_*.                     \tag{9.7}
\]

Multiplying by `M(p)`, summing `p`, and using (7.8) gives

\[
 W_{PP}:=\sum_{p,p'\in P}M(p)M(p'){
 \gcd(p,p')\over\max(p,p')}
 <{A_*\over2}N^4.                                     \tag{9.8}
\]

Similarly, for fixed `c in C`,

\[
 \sum_{p\in P}M(p){\gcd(c,p)\over\max(c,p)}
 \le4\,20^4\mathcal S_4
 ={345708800000\over19683}=:B_*.                       \tag{9.9}
\]

Using (7.7), symmetry of the kernel, and `N^3<=N^4`,

\[
 W_{CP}+W_{PC}<2B_*N^4.                               \tag{9.10}
\]

Equations (9.7)-(9.10) settle every sector containing a primitive four-token
value. Lemma 8.1 used the full reduced ratio, not an approximation based on
decimal valuation.

## 10. Cancellation-cancellation sector

Every positive cancellation value has the unique form

\[
 D_{v,r}=10^v(10^r-1),\qquad v\ge0,\ r\ge1,\ v+r<N.   \tag{10.1}
\]

For two such values, (5.5) and coprimality with 10 give the exact formula

\[
 \gcd(D_{v,r},D_{w,s})
 =10^{\min(v,w)}(10^{\gcd(r,s)}-1).                    \tag{10.2}
\]

Using `10^j-1<10^j` and `10^j-1>=9*10^(j-1)`, the kernel is at most

\[
 {10\over9}
 10^{\min(v,w)+\min(r,s)-\max(v+r,w+s)}.               \tag{10.3}
\]

For `X=v-w` and `Y=r-s`, the negative of the exponent in (10.3) is

\[
 {|X|+|Y|+|X+Y|\over2}\ge\max(|X|,|Y|).               \tag{10.4}
\]

There are exactly `8j` integer lattice points at Chebyshev distance `j>=1`.
Enlarging the legal `(w,s)` triangle to the full lattice therefore yields,
for each fixed `(v,r)`,

\[
 \begin{aligned}
 \sum_{w,s}{\gcd(D_{v,r},D_{w,s})\over
                   \max(D_{v,r},D_{w,s})}
 &\le {10\over9}\left(1+\sum_{j=1}^{\infty}8j10^{-j}\right)\\
 &={10\over9}\left(1+{80\over81}\right)
 ={1610\over729}.
 \end{aligned}                                        \tag{10.5}
\]

Since every inner multiplicity is at most `2N`, and (7.7) bounds the outer
multiplicity sum,

\[
 \boxed{W_{CC}< {3220\over729}N^4.}                   \tag{10.6}
\]

## 11. The weighted-GCD theorem and Tail(t)

Combining (9.8), (9.10), and (10.6),

\[
 \begin{aligned}
 W&:=\sum_{d,e>0}M(d)M(e){\gcd(d,e)\over\max(d,e)}\\
 &<\left({A_*\over2}+2B_*+{3220\over729}\right)N^4\\
 &={11316017134946\over19683}N^4
 <574913232N^4.
 \end{aligned}                                        \tag{11.1}
\]

Thus the absolute, all-parameter estimate

\[
 \boxed{W\le C_*N^4,\qquad C_*=574913232}              \tag{11.2}
\]

holds for every positive `m,N`. From (6.6), using
`floor(x)<=x`,

\[
 \operatorname{Var}(E)\le2C_*HN^4.                    \tag{11.3}
\]

Fix any real `0<t<1`. On the event `A>2HT_t`, (4.6) gives

\[
 E\ge {A^2\over H}>4HT_t^2.                           \tag{11.4}
\]

Since `|Q|<=N^2<=T_t^2`,

\[
 E-H|Q|>3HT_t^2.                                      \tag{11.5}
\]

Chebyshev's inequality and (11.3) now give

\[
 \begin{aligned}
 \operatorname{Leb}\{A>2HT_t\}
 &\le {2C_*HN^4\over9H^2T_t^4}\\
 &= {2C_*/9\over H(1+NH^{-t})^4}\\
 &=\boxed{{127758496\over H(1+NH^{-t})^4}}.
 \end{aligned}                                        \tag{11.6}
\]

This proves the exact `Tail(t)` inequality (2.6), for every real `0<t<1`,
with the constants in (2.7).

## 12. All-integer, dyadic, and Borel-Cantelli closure

Fix a rational `t in (0,1)` and define the measurable event

\[
 \mathrm{Bad}_{m,N,t}
 =\{\alpha\in[0,1):A(\alpha;m,N)>2H_mT_t(m,N)\}.       \tag{12.1}
\]

It is measurable because `A` is a finite sum of absolute values of
trigonometric polynomials. Set `x=H^{-t}`. Since
`N -> (1+Nx)^(-4)` is decreasing,

\[
 \sum_{N=1}^{\infty}(1+Nx)^{-4}
 \le\int_0^\infty(1+xy)^{-4}\,dy
 ={H^t\over3}.                                        \tag{12.2}
\]

For an explicit dyadic audit, partition the same all-integer sum into the
disjoint slabs `2^j<=N<2^(j+1)`. Tail(t) gives

\[
 \sum_{N=2^j}^{2^{j+1}-1}\operatorname{Leb}(\mathrm{Bad}_{m,N,t})
 \le {127758496\,2^j\over
 H(1+2^jH^{-t})^4}.                                   \tag{12.3}
\]

This is a partition of the actual events for every integer `N`; it does not
assert monotonicity of `A` or replace a slab by its endpoint. For completeness,
if `2^J<=H^t<2^(J+1)`, then

\[
 \sum_{j=0}^{J}{2^j\over(1+2^jH^{-t})^4}
 \le\sum_{j=0}^{J}2^j<2^{J+1}\le2H^t.                 \tag{12.4}
\]

For `j=J+1+k`, one has

\[
 {2^j\over(1+2^jH^{-t})^4}
 \le H^t\left({H^t\over2^j}\right)^3
 <H^t2^{-3k}.
\]

The remaining geometric tail is therefore at most `8H^t/7`, so the dyadic
series is finite. The sharper direct estimate (12.2) gives

\[
 \begin{aligned}
 \sum_{m=1}^{\infty}\sum_{N=1}^{\infty}
 \operatorname{Leb}(\mathrm{Bad}_{m,N,t})
 &\le {127758496\over3}
 \sum_{m=1}^{\infty}H^{t-1}\\
 &= {127758496\over3}
 {10^{-(1-t)}\over1-10^{-(1-t)}}<\infty.
 \end{aligned}                                        \tag{12.5}
\]

The first Borel-Cantelli lemma, which requires no independence, shows that
for almost every `alpha`, only finitely many integer pairs `(m,N)` violate
`A<=2HT_t`. For such an `alpha`, define

\[
 B_{\alpha,t}=\max\left(2,
 \max_{(m,N)\ \mathrm{exceptional}}
 {A(\alpha;m,N)\over H_mT_t(m,N)}\right),              \tag{12.6}
\]

omitting the inner maximum when the exceptional set is empty. It is a maximum
over finitely many finite values, and it is chosen before all positive
`m,N`. Therefore

\[
 A(\alpha;m,N)\le B_{\alpha,t}H_mT_t(m,N)             \tag{12.7}
\]

simultaneously for every positive `m,N`.

Intersect these full-measure sets only over the countable rationals
`t in (0,1)`. Given any real `s in (0,1)`, choose a rational `t` with
`s<t<1`. Then

\[
 H_m^{-t}\le H_m^{-s},\qquad T_t(m,N)\le T_s(m,N).     \tag{12.8}
\]

The constant `B_(alpha,t)` from (12.7) consequently works for the real
exponent `s` as well. We have proved the exact almost-everywhere sibling:

\[
 \boxed{
 \begin{gathered}
 \text{There is a measurable }\Omega\subseteq[0,1)
 \text{ with }\operatorname{Leb}(\Omega)=1\text{ such that}\\
 \forall\alpha\in\Omega\ \forall s\in\mathbb R\ (0<s<1)\\
 \exists B_{\alpha,s}\ge1\ \forall m,N\ge1,\\
 \sum_{h=1}^{10^m}|S_h(\alpha;m,N)|
 \le B_{\alpha,s}10^m\bigl(N+N^2 10^{-sm}\bigr).
 \end{gathered}}                                       \tag{12.9}
\]

## 13. Verdict

The exact displayed `Tail(t)` inequality from the T14 note is true for the
scale-matched L1 almost-everywhere phase sibling. Explicitly, it holds for all
real `0<t<1`, all positive `m,N`, with

\[
 (K_t,C_t,p_t)=(2,127758496,4).
\]

The proof retains the restricted ordered T8 domain, inclusive frequency
endpoint `10^m`, every 10-adic primitive chain, all four signed-decimal
weighted-GCD sectors, and every ordinary gcd factor. Section 12 completes
the countable-exponent, dyadic-all-`N`, and Borel-Cantelli quantifiers.

This is only an almost-everywhere phase sibling. It makes no assertion for the
fixed value `alpha=pi`, no assertion about the decimal digits of pi, and no
assertion about C1.
