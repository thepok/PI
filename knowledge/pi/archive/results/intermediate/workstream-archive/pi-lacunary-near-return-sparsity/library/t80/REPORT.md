# T80: Ramanujan 1914 reciprocal-series audit at the fixed-pi frontier

Date: 2026-08-09 UTC.

Status: `proof sketch`. The primary-source check is dated and byte-pinned in
`SOURCE_PINS.md`. The universal arithmetic arguments below are inspectable
prose proofs, not Lean theorems. The finite replay is an `experiment` and is
not evidence for C1, C2, or the canonical question.

## 1. Exact scope

The delivered `canonical_statement.txt` is a byte-exact copy of the immutable
statement and has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N >= 1`, the target is

\[
 Q_\pi(n,N)=\#\{(i,j):0\le i,j<N,
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{1.1}
\]

Pairs are ordered, all `N` diagonal pairs are included, and the inequality is
strict. The canonical quantifiers are

\[
 \forall A\ge1\ \exists n_0\ge1\ \forall n\ge n_0\ \exists N\ge1:
 A n Q_\pi(n,N)\le N^2.
\tag{1.2}
\]

No quantifier, base, radius, pair convention, or fixed value of `pi` is
changed below.

The new premise is Ramanujan's equation (44), converted exactly to

\[
 {1\over\pi}={2\sqrt2\over9801}
 \sum_{k=0}^{\infty}
 { (4k)!(1103+26390k)\over(k!)^4 396^{4k}}.
\tag{1.3}
\]

It is tested only as an algebraic-modular route to the accepted fixed-pi
frontiers.

## 2. Endpoints stated before derivation

**SUCCESS endpoint.** For one named accepted frontier, derive a truncation
`pi_K` and a uniform algebraic-modular estimate for every required orbit
length and frequency, with approximation error smaller than an explicit
strict margin. For T10 this means bounding every required algebraic sum by
half of T10's resonance threshold and spending the other half on truncation
error.

**FALSIFICATION endpoint.** Exhibit, at the literal T10 orbit range, a
denominator, ideal, transient, order, orbit-length, collision, or inversion
error that prevents the selected algebraic-modular premise from controlling
the real character modulo `Z`. The endpoint must be a proved mismatch, not a
statement that residue occupancy is unknown.

## 3. Accepted frontiers consulted

The following files are `machine-checked` library artifacts. Their comments
explicitly deny any fixed-pi conclusion not present in their theorem types.

| item | SHA-256 | exact interface used |
|---|---|---|
| T7 `T7FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | `E_pi <= Q_pi <= 3 E_pi` and the exact finite-energy formulation equivalent to (1.2) |
| T10 `T10LongLagResonance.lean` | `63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947` | under its explicit positivity, large-`N`, radius, and discrepancy hypotheses, the resonance branch supplies `1<=h<=256An` whose length-`N-r` sum exceeds `(N-r)/(131072 A^2 n^2)`; its final failure-of-canonical theorem arranges those hypotheses |
| T55 `T55SignedMultiplierTenPairing.lean` | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | exact endpoint/top-shell split; `TopShellCorrelationHypothesis` is expressly unproved |
| T61 `T61DirectLabelAdjacentPhaseVariance.lean` | `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb` | exact direct-label variance identity; its strict variance premise is expressly unproved |

This audit selects T10 because (1.3) directly approximates each real phase.
It does not silently treat the conditional T55 or T61 premise as accepted
cancellation.

## 4. T79 non-overlap and negative-entry table

The status column is essential. A prior note at `proof sketch` level is not a
discharged premise here.

| audited family or semantic card | status consulted | prior negative entry | why (1.3) is not that family |
|---|---|---|---|
| T63 standard BBP formula | `literature-checked` applicability audit; T63 report SHA-256 `28e7bdc28628404532afcecda50ed954836df3eb7d6578315604907a7f10ad59` | base 16; the source leaves decimal pi open | (1.3) is a base-free hypergeometric reciprocal identity with algebraic factor `sqrt(2)`, not a base-16 digit extractor |
| T63 Zudilin recurrence/arctangent formula | same T63 status | corrected source removes the invalid decimal congruence; rational truncation transfers phases but creates no cancellation | coefficients and denominators in (1.3) are different, and inversion puts the truncation in `Q(sqrt(2))` rather than `Q` |
| T63 Bailey-Crandall/Lagarias route | source-pinned theorems and hypotheses | rational phase theorem requires a coprime pure-power modulus; dynamical statements are conditional or equivalences | no Bailey-Crandall theorem is imported; its finite rational orbit premise already fails because `pi_K` is irrational |
| T68 corrected-Zudilin transient | machine-checked, Lean SHA-256 `c0076582b930b24adf29d84e84526fa9db0c28a9f20309cf4808ded31ec69479` | the displayed Zudilin exponent and positive-tail length conditions are incompatible | T68 is explicitly route-specific; Sections 8-11 below independently compute the new denominator ideal and both base-10 valuations |
| T78 Euler-Li-Rabinowitz-Wagon series | `proof sketch`, report SHA-256 `26cc36a18ea585d85d5e7f2c23e40df61bbb1ca94639541736531feb8074af4b` | rational factorial truncations have an explicit square-root-modulus scale obstruction | (1.3) has broad factorial/hypergeometric overlap, but its exact reciprocal truncations are algebraic irrational; T78 does not audit their denominator ideals or quotient kernel |
| T79's Chudnovsky-type factorial exclusion | `proof sketch` inventory entry, not a proved T78 conclusion | grouped broadly with factorial opportunities without a Ramanujan-1914 calculation | no total family non-overlap is claimed; the new premise is specifically the `Q(sqrt(2))` reciprocal-truncation order bridge, which that entry neither states nor calculates |
| T79 Abrarov-Quine Machin specialization | `proof sketch`, report SHA-256 `7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800` | rational truncations have a forced prime-power cofactor with square root larger than the orbit length | no Machin identity or prime `147153121` occurs here; the truncations below lie in `Q(sqrt(2))` |
| T79 BBP, Zudilin, Bailey-Crandall PRNG, and Euler/factorial exclusions | `proof sketch` inventory | marked previously covered, with T78 correctly treated as unverified prose | the first six rows document the independent check rather than inheriting the inventory conclusion |
| exact-computation semantic card | canonical verification rule and T17/T65 notes | finite exact phases do not establish adaptive-frequency cancellation | the replay is labeled `experiment`; every universal obstruction is proved symbolically below |
| modular-orbit semantic card | T63/T65/T78/T79 notes | order and equality collisions alone are not an exponential-sum bound | Sections 10-11 calculate both quotients and prove exactly why the finite order is not a real phase order |
| equivalent-reformulation semantic card | canonical ambiguities and T60/T67 | invariant identities, Walsh energy, and terminal shells cannot be renamed as fixed-pi cancellation | this note substitutes constants into T10's literal sum and ends negatively rather than proposing a renamed hypothesis |

Thus the exact selected premise, namely that the finite denominator-ideal
order of the quadratic-irrational reciprocal truncations controls T10's real
phases, is absent from every audited entry. There is acknowledged structural
factorial/hypergeometric overlap with T78/T79; distinct coefficients alone are
not presented as non-overlap. The semantic warnings remain applicable and are
tested rather than cited as proofs.

## 5. Primary source and exact modernization

Ramanujan, "Modular equations and approximations to pi," *Quarterly Journal
of Pure and Applied Mathematics* 45 (1914), 350-372, prints equation (44) on
printed p. 370. The delivered 1927 collected-paper scan has the same equation
on PDF p. 74 / collected-paper p. 38. Its SHA-256 is

```text
858af6247df93916a2ef7cedfe774782e95acbb9c06fe40a876c06ff0add41a7
```

The searchable primary-article typesetting has SHA-256

```text
478e2643fd7ca8a2dbbba23b60ae35608845c21d29019bb9d8dd9b0af27710a1
```

and displays equation (44) on PDF p. 22 / article p. 47. URLs, extraction
hashes, and visual-page hashes are in `SOURCE_PINS.md`.

Equation (44) uses expanded product notation. Its `k`th product factor is

\[
 { (1/4)_k(1/2)_k(3/4)_k\over(k!)^3}
 ={(4k)!\over256^k(k!)^4}.
\tag{5.1}
\]

The coefficient progression is `1103+26390k`, and `99^2=9801`. Since

\[
 256^k99^{4k}=(4\cdot99)^{4k}=396^{4k},
\tag{5.2}
\]

Ramanujan's displayed equation is

\[
 {1\over2\pi\sqrt2}={1\over9801}\sum_{k\ge0}
 { (4k)!(1103+26390k)\over(k!)^4 396^{4k}}.
\tag{5.3}
\]

Multiplication by `2 sqrt(2)` gives (1.3). The replay verifies (5.1) for
`0<=k<=20`; the displayed factorial identity itself follows by grouping the
four residue classes in `(4k)!` and is universal.

## 6. Reciprocal-series tail

Define

\[
 t_k={ (4k)!(1103+26390k)\over(k!)^4 396^{4k}},\qquad
 S_K=\sum_{k=0}^{K-1}t_k,\qquad R_K=\sum_{k=K}^{\infty}t_k
\tag{6.1}
\]

for `K>=1`. All terms are positive. Exactly,

\[
 {t_{k+1}\over t_k}=
 {\prod_{r=1}^4(4k+r)\over(k+1)^4 396^4}
 {1103+26390(k+1)\over1103+26390k}.
\tag{6.2}
\]

For each `r`, `(4k+r)/(k+1)<=4`, while

\[
 {1103+26390(k+1)\over1103+26390k}
 \le {27493\over1103}<25.
\tag{6.3}
\]

Consequently

\[
 0<{t_{k+1}\over t_k}< {256\cdot25\over396^4}
 ={25\over99^4}={25\over96059601}<{1\over3000000}=:q.
\tag{6.4}
\]

Since `t_0=1103`, geometric summation gives the rigorous reciprocal tail

\[
 0<R_K<{1103q^K\over1-q}<1104q^K.
\tag{6.5}
\]

No finite computation is used in (6.2)-(6.5).

## 7. Inversion into the actual coefficient ring

Set

\[
 x_K={2\sqrt2\over9801}S_K,
 \qquad \pi_K=x_K^{-1}={9801\over2\sqrt2 S_K}.
\tag{7.1}
\]

The full reciprocal is

\[
 {1\over\pi}={2\sqrt2\over9801}(S_K+R_K).
\tag{7.2}
\]

Direct subtraction, without a formal power-series inversion, gives

\[
 \boxed{\pi_K-\pi={9801\over2\sqrt2}
 {R_K\over S_K(S_K+R_K)}.}
\tag{7.3}
\]

Thus `pi_K>pi`. Since `S_K>=1103`, `S_K+R_K>1103`, and `sqrt(2)>1`, (6.5)
implies

\[
 0<\pi_K-\pi
 <{9801\cdot1104\over2\cdot1103^2}q^K
 <5q^K<5\cdot10^{-6K}.
\tag{7.4}
\]

This accounts for the reciprocal-tail amplification explicitly.

## 8. Uniform literal-pair schedule

For `N,n>=1`, choose

\[
 \boxed{K(N,n)=\left\lceil{N+n\over6}\right\rceil.}
\tag{8.1}
\]

For all `0<=i,j<N`, `|10^i-10^j|<10^{N-1}`. Equations (7.4) and (8.1)
therefore give

\[
 |(10^i-10^j)(\pi_K-\pi)|
 <5\,10^{N-1-6K}\le {1\over2}10^{-n}.
\tag{8.2}
\]

Circle distance is 1-Lipschitz, so

\[
 \left|\|(10^i-10^j)\pi_K\|_{\mathbb R/\mathbb Z}
 -\|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}\right|
 <{1\over2}10^{-n}
\tag{8.3}
\]

simultaneously for every literal ordered pair. This gives a half-radius
safety transfer, not an equality between the two strict predicates at their
common boundary.

## 9. Reduced denominator and denominator ideal

A convenient common denominator for the `K` terms is

\[
 D_K=((K-1)!)^4 396^{4(K-1)}.
\tag{9.1}
\]

Indeed

\[
 P_K=\sum_{k=0}^{K-1}(4k)!(1103+26390k)
 \left({(K-1)!\over k!}\right)^4 396^{4(K-1-k)}\in\mathbb Z
\tag{9.2}
\]

and `S_K=P_K/D_K`. Let `H_K=gcd(P_K,D_K)`, `A_K=P_K/H_K`, and
`B_K=D_K/H_K`. Then `S_K=A_K/B_K` in lowest terms. By (7.1),

\[
 \pi_K={9801B_K\over4A_K}\sqrt2={a_K\over b_K}\sqrt2,
 \qquad \gcd(a_K,b_K)=1,
\tag{9.3}
\]

where the last fraction is reduced. The actual coefficient field is
`Q(sqrt(2))`; its ring of integers is

\[
 \mathcal O=\mathbb Z[\sqrt2].
\tag{9.4}
\]

For any reduced `x=(a/b)sqrt(2)`, define the denominator ideal

\[
 \mathfrak d(x)=\{z\in\mathcal O:zx\in\mathcal O\}.
\tag{9.5}
\]

Writing `z=u+v sqrt(2)`, one has

\[
 zx={2av\over b}+{au\over b}\sqrt2.
\tag{9.6}
\]

Because `gcd(a,b)=1`, membership in (9.5) is equivalent to `b|u` and
`b|2v`. With `delta=gcd(b,2)`, this proves

\[
 \boxed{\mathfrak d(x)=b\mathbb Z\oplus{b\over\delta}\mathbb Z\sqrt2
 =\left(b,{b\over\delta}\sqrt2\right),\qquad
 N\mathfrak d(x)={b^2\over\delta}.}
\tag{9.7}
\]

In particular the even-denominator ideal is not silently replaced by `(b)`.
Also `d(x) intersect Z=bZ`, so integer multipliers have exact annihilator `b`.

## 10. Two-five transient, order, orbit length, and collisions

Suppress `K` and write `pi_K=(a/b)sqrt(2)` in reduced form. Factor

\[
 b=2^\alpha5^\beta m,\qquad \gcd(m,10)=1,
 \qquad L=\max(\alpha,\beta).
\tag{10.1}
\]

The power-of-2 component is consumed exactly after `alpha` multiplications by
10, and the power-of-5 component exactly after `beta`. For `m>1`, set

\[
 T=\operatorname{ord}_m(10);
\tag{10.2}
\]

for `m=1`, set `T=1`. Since `gcd(a,b)=1`, for `0<=i<j`,

\[
 a10^i\equiv a10^j\pmod b
 \quad\Longleftrightarrow\quad b\mid10^i(10^{j-i}-1).
\tag{10.3}
\]

The second factor is coprime to 10. The Chinese remainder theorem therefore
gives the exact criterion

\[
 \boxed{a10^i\equiv a10^j\pmod b
 \quad\Longleftrightarrow\quad i\ge L\ \hbox{ and }\ T\mid(j-i).}
\tag{10.4}
\]

Thus the coefficient orbit, and equivalently the orbit in
`Q(sqrt(2))/Z[sqrt(2)]`, has exact preperiod `L`, exact period `T`, and
`L+T` distinct states.

For a prefix of length `N`, put `M=(N-L)_+` and

\[
 c_r=\max\left(0,1+\left\lfloor{M-1-r\over T}\right\rfloor\right)
 \quad(0\le r<T).
\tag{10.5}
\]

No early state collides with any other state, so the exact ordered coefficient
collision count is

\[
 \boxed{\min(N,L)+\sum_{r=0}^{T-1}c_r^2.}
\tag{10.6}
\]

The replay verifies these reduced data and exact orders:

| K | a_K | b_K | alpha | beta | m | ord_m(10) |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 9801 | 4412 | 2 | 0 | 1103 | 1102 |
| 2 | 2510613731736 | 1130173253125 | 0 | 5 | 361655441 | 12912240 |
| 3 | 2286635172367940241408 | 1029347477390786609545 | 0 | 1 | 205869495478157321909 | 1944481966883820 |
| 4 | 17252765328978109815564789153792 | 7766473062254307011793347201855 | 0 | 1 | 1553294612450861402358669440371 | 333008626063235355784320 |

For `K=1,N=2500`, (10.6) gives 5880 coefficient collisions, and exhaustive
enumeration agrees. This is a sanity check, not a universal proof.

## 11. Literal orbit and collision calculation

The accepted frontiers do not use the quotient by `Z[sqrt(2)]`. They use the
real character

\[
 e(y)=\exp(2\pi i y),\qquad \ker e=\mathbb Z.
\tag{11.1}
\]

If `i<j` and the literal circle orbit collided, then

\[
 10^j\pi_K-10^i\pi_K
 ={a(10^j-10^i)\over b}\sqrt2\in\mathbb Z.
\tag{11.2}
\]

Its rational coefficient is nonzero, so the left side is irrational. This is
impossible. Hence

\[
 \boxed{10^i\pi_K\equiv10^j\pi_K\pmod1\Longleftrightarrow i=j.}
\tag{11.3}
\]

The literal real and circle orbits therefore have infinite orbit length. Their
exact ordered equality-collision count in every prefix of length `N` is `N`,
the diagonal only. This differs from (10.6).

More explicitly, for every `i>=L`, coefficient periodicity says

\[
 10^{i+T}-10^i=bq_i,\qquad q_i\in\mathbb Z_{>0}\quad(i\ge L).
\tag{11.4}
\]

But the corresponding phase ratio at any nonzero integer frequency `h` is

\[
 {e(h10^{i+T}\pi_K)\over e(h10^i\pi_K)}
 =e(haq_i\sqrt2)\ne1.
\tag{11.5}
\]

Thus the real character is nontrivial on `sqrt(2) in Z[sqrt(2)]` and does not
descend to the finite algebraic quotient. Equations (11.3)-(11.5) are the
literal obstruction; no occupancy estimate is left as a premise.

## 12. Quantitative substitution into T10

Start with a literal output of T10's resonance branch: `A,n>=1`,
`r in Icc(1,N-1)`, `J=N-r>0`, `1<=h<=256An`, and T10's radius,
large-`N`, and discrepancy hypotheses already discharged by its
machine-checked theorem. This note does not claim that an arbitrary bad finite
scale has those hypotheses. For real `theta`, define

\[
 \mathcal L_{N,r,h}(\theta)=
 \sum_{j=0}^{J-1}e\left(h10^j(10^r-1)\theta\right).
\tag{12.1}
\]

The elementary inequality `|e(x)-e(y)|<=2 pi |x-y|` and geometric summation
give

\[
 |\mathcal L_{N,r,h}(\pi)-\mathcal L_{N,r,h}(\pi_K)|
 \le {2\pi |h|(10^r-1)(10^J-1)\over9}|\pi-\pi_K|.
\tag{12.2}
\]

Using (7.4), `pi<4`, `r+J=N`, and T10's `1<=h<=256An`,

\[
 |\mathcal L(\pi)-\mathcal L(\pi_K)|
 <{10240\over9}An\,10^{N-6K}.
\tag{12.3}
\]

T10's machine-checked resonance threshold is

\[
 {J\over131072A^2n^2}<|\mathcal L_{N,r,h}(\pi)|.
\tag{12.4}
\]

To spend half the threshold on approximation, a lag-adapted sufficient
condition is

\[
 \boxed{10^{6K-N}\ge {300000000 A^3n^3\over J}.}
\tag{12.5a}
\]

For a single integer schedule uniform over every legal lag, define

\[
 d(A,n)=\min\{d\in\mathbb N:300000000A^3n^3\le10^d\},\qquad
 K_{10}(A,n,N)=\left\lceil{N+d(A,n)\over6}\right\rceil.
\tag{12.5b}
\]

The defining set for `d(A,n)` is nonempty. Since `J>=1`, (12.5b) implies
(12.5a) simultaneously for every T10 lag. Indeed
`300000000 > 10240*262144/9`, so (12.3) is then strictly less than
`J/(262144 A^2 n^2)`. A successful Ramanujan bridge would still have to prove

\[
 |\mathcal L_{N,r,h}(\pi_K)|\le {J\over262144A^2n^2}
\tag{12.6}
\]

uniformly for the literal T10 labels. Equations (12.2)-(12.6) are the promised
quantitative substitution, including every exponent and constant. The finite
order `T` in (10.2) cannot turn (12.6) into a complete-period or root-of-unity
estimate, because (11.5) shows that it is not a period of any summand. This
does not exclude a different analytic estimate that uses the remaining
quadratic-irrational phases without asserting periodicity.

## 13. Replay and non-claims

From a directory containing only the delivered artifacts, run

```text
python3 verify_note.py
```

The standard-library script verifies the complete hash manifest, the
product-to-factorial conversion, exact partial sums, reduced `a_K,b_K`, both
valuations, coprime cofactors, exact orders from their prime divisors,
denominator-ideal norms, and (10.6) by enumeration for `K=1,N=2500`.
`raw_output.txt` records the run. `SHA256SUMS` closes the artifact set.

Finite checks prove no universal claim. This note proves no normality,
equidistribution, T55 top-shell premise, T61 variance premise, C1, C2, or
canonical estimate. It does not exclude a future analytic estimate for
lacunary sums at quadratic irrational arguments. It falsifies only the
specific premise that Ramanujan truncation plus denominator-ideal order gives
a finite periodic phase orbit usable by a complete-period T10 estimate.

## 14. Representation-specific obstruction

For every `K>=1`, the reciprocal truncation is
`pi_K=(a_K/b_K)sqrt(2)`. The obstruction is specifically to the proposed
finite-quotient/order bridge; it is not a claim against every analytic use of
Ramanujan's identity.

\[
\boxed{\begin{aligned}
i\ge L_K:\quad
&10^{i+T_K}\pi_K-10^i\pi_K=a_Kq_i\sqrt2
   \in\mathbb Z[\sqrt2]\setminus\mathbb Z,\\
&e(h10^{i+T_K}\pi_K)\ne e(h10^i\pi_K)\qquad(h\in\mathbb Z\setminus\{0\}),\\
&\ker(e|_{\mathbb Z[\sqrt2]})=\mathbb Z,
  \quad\mathfrak d(\pi_K)\not\subseteq\ker e,\\
&\therefore\ \operatorname{ord}_{m_K}(10)
  \text{ is not a T10 phase period and cannot yield (12.6) by finite-period
  decomposition.}
\end{aligned}}
\tag{14.1}
\]
