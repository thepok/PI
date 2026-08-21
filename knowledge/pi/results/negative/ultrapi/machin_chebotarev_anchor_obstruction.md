# Chebotarev obstruction to exact Machin denominator anchors

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No fixed return and no proof that every finite decimal word occurs in pi was
obtained.  Canonical V1 remains a `conjecture`.

There is, however, a new unconditional **odd-prime strengthening** of an
already known route closure.  Let

\[
 M_j=\operatorname{machinLowerRat}(3j)
\]

be the exact rational Machin truncation used by T38, and let its decimal-scaled
version be

\[
 R_j=10^jM_j
     =\operatorname{sampledMachinValueRat}(j).                 \tag{1}
\]

Then for all sufficiently large \(j\), and for **every** \(m\geq0\),

\[
              (10^m-16)M_j\notin\mathbb Z.                    \tag{2}
\]

Equivalently, the reduced denominator of \(M_j\) never divides any
\(10^m-16\) once \(j\) is large.  Thus the natural all-depth sampled Machin
family cannot satisfy the strongest synchronized-return construction

\[
 (10^{m_j}-16)M_{j}∈\mathbb Z,
 \qquad |\pi-M_j|=o(10^{-m_j}).                               \tag{3}
\]

Exact fixed-sixteen synchronization of this family was already excluded more
simply by its growing decimal-primary denominator.  The result here is not
the first exclusion of (3): it proves that, even after setting aside that
5-primary obstruction, a varying odd prime independently kills every exact
anchor.  This matters for diagnosing denominator-safe variants, but is not
by itself a new route to V1.

The proof combines two independently inspectable inputs.

1. A `literature-checked` application of the unconditional Chebotarev density
   theorem produces, in every sufficiently large interval \((x/2,x]\), a
   prime \(p\) for which \(10\) is a sixteenth power modulo \(p\), but
   \(16\) is not.  Hence \(10^m\not\equiv16\pmod p\) for every \(m\).
2. The `machine-checked` T48 theorem says that every sufficiently large prime
   in the upper half of the actual Machin Taylor window occurs exactly once
   in the reduced denominator of \(R_j\).

This proves (2) as a `proof sketch` assembled from a published theorem and a
machine-checked local theorem.  The companion finite replay is an
`experiment`.  The result excludes **exact denominator synchronization for
this Machin family only**.  It gives no useful Archimedean lower bound for the
nonzero rational phase, so it does not exclude

\[
              \|(10^m-16)M_j\|_{\mathbb T}\longrightarrow0    \tag{4}
\]

without exact integrality, and does not prove the fixed return or V1.

## 1. Exact target and the scope of the obstruction

The audited T69/Furstenberg bridge reduces V1 to

\[
       \liminf_{m\to\infty}\|(10^m-16)\pi\|_{\mathbb T}=0.    \tag{5}
\]

If rational shadows \(A_j\) obey

\[
 (10^{m_j}-16)A_j\in\mathbb Z,
 \qquad |\pi-A_j|=o(10^{-m_j}),                               \tag{6}
\]

then (5) follows by the triangle inequality.  The first condition in (6) is
equivalent to the reduced denominator of \(A_j\) dividing
\(10^{m_j}-16\).  Finding (6) would already give V1; it is not a routine
intermediate lemma.

The present report proves that the particular shadows \(A_j=M_j\) cannot pay
the exact-divisibility entry in (6), no matter how \(m_j\) is chosen.  It does
not address a different rational family, a signed depth-varying identity, or
the nonzero residue option in (4).

## 2. A positive-density set of permanently incompatible primes

Let \(\zeta_{16}\) be a primitive sixteenth root of unity and set

\[
 \begin{aligned}
 F&=\mathbb Q(\zeta_{16}),\\
 K&=\mathbb Q(\zeta_{16},10^{1/16}),\\
 E&=\mathbb Q(\zeta_{16},2^{1/4}),\\
 L&=KE.
 \end{aligned}                                               \tag{7}
\]

These are finite Galois extensions of \(\mathbb Q\).  More precisely,
\(K/F\) and \(E/F\) are the relative splitting fields of
\(X^{16}-10\) and \(X^4-2\), respectively; over \(\mathbb Q\), \(E\)
is the splitting field of \(\Phi_{16}(X)(X^4-2)\), not of
\(X^4-2\) alone.  The compositum is \(L\).

The strict containment \(K\subsetneq L\) has a small exact certificate.  Put

\[
                         p_0=5521=16\cdot345+1.              \tag{8}
\]

Trial division certifies that \(p_0\) is prime, and exact modular
exponentiation gives

\[
            10^{345}\equiv1\pmod {5521},\qquad
            2^{1380}\equiv-1\pmod {5521}.                   \tag{9}
\]

Because \(\mathbb F_{5521}^{\times}\) is cyclic of order \(5520\), the first
congruence says that \(10\) is a sixteenth power, whereas the second says
that \(2\) is not a fourth power.  Thus \(p_0\) splits completely in \(K\)
but not in \(E\).  Only 2 and 5 can ramify in this fixed
Kummer--cyclotomic compositum, so \(p_0\) is unramified in \(K\), \(E\),
and \(L\).  Therefore \(E\not\subset K\), proving \(K\subsetneq L\).
In fact,

\[
 [K:\mathbb Q]=128,\qquad [E:\mathbb Q]=16,
 \qquad [L:\mathbb Q]=256.                                 \tag{9a}
\]

Here \([K:F]=16\) follows by Eisenstein at a prime of \(F\) above 5,
while \([E:F]=2\) because \(\sqrt2\in F\) but
\(\mathbb Q(2^{1/4})\) cannot be an intermediate field of the abelian
extension \(F/\mathbb Q\): that real quartic field is not Galois.  The
splitting witness then gives \(K\cap E=F\) and the degree of \(L\).

Define \(\mathcal P\) to be the rational primes unramified in \(L\) that
split completely in \(K\) but not in \(L\).  The split-completely primes
of \(L\) are a subset of those of \(K\).  Chebotarev therefore gives

\[
 \#\{p\le x:p\in\mathcal P\}
  =\left({1\over[K:\mathbb Q]}-{1\over[L:\mathbb Q]}\right)
      \operatorname{Li}(x)+o(\operatorname{Li}(x)).           \tag{10}
\]

The coefficient is explicitly

\[
 \delta={1\over[K:\mathbb Q]}-{1\over[L:\mathbb Q]}
       ={1\over256}>0.                                      \tag{11}
\]

Subtracting (10) at \(x\) and \(x/2\)
gives

\[
 \#\{x/2<p\le x:p\in\mathcal P\}
  \sim \delta\{\operatorname{Li}(x)-\operatorname{Li}(x/2)\}
  \sim {\delta x\over2\log x}.                              \tag{12}
\]

In particular, every sufficiently large interval \((x/2,x]\) contains a
prime in \(\mathcal P\).  No effective threshold is needed below.

Every \(p\in\mathcal P\) is permanently incompatible with the fixed-sixteen
congruence.  Indeed, splitting in \(K\) implies

\[
 p\equiv1\pmod {16},\qquad 10\in(\mathbb F_p^\times)^{16}.   \tag{13}
\]

If \(2\) were a fourth power modulo \(p\), then \(X^4-2\) would split because
\(\mu_4\subset\mathbb F_p\).  The prime would split in both \(K\) and \(E\),
and hence in \(L\), contrary to its definition.  Thus

\[
                         2\notin(\mathbb F_p^\times)^4.       \tag{14}
\]

If \(10^m\equiv16\pmod p\), then the left side is a sixteenth power by
(13), so \(16=2^4\) is a sixteenth power.  Raising to the
\((p-1)/16\)-th power would give

\[
                         2^{(p-1)/4}=1,                       \tag{15}
\]

which in the cyclic group \(\mathbb F_p^\times\) is equivalent to \(2\)
being a fourth power.  This contradicts (14).  Consequently

\[
          \boxed{\ 10^m\not\equiv16\pmod p
                    \quad\text{for every }m\ge0\ }           \tag{16}
\]

for every \(p\in\mathcal P\).

Boundary notes:

- The set \(\mathcal P\) is defined by splitting, not by an unproved Artin
  primitive-root conjecture.
- The positive density and dyadic-interval consequence are unconditional;
  the number fields are fixed.
- Equation (16) uses only a sufficient bad-prime class.  There are additional
  primes at which \(16\notin\langle10\rangle\), but they are unnecessary.

## 3. The actual Machin denominator contains one such prime

For \(N\ge0\), put

\[
 d_N=12N+15,
 \qquad R_{N+1}=10^{N+1}M_{N+1}
   =\operatorname{sampledMachinValueRat}(N+1).                \tag{17}
\]

The `machine-checked` theorem
`padicValNat_sampledMachinValueRat_den_upperHalfPrime` in
[`T48T48MachinSeedUpperHalfPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T48T48MachinSeedUpperHalfPrimeSurvival.lean)
states that if \(p\) is prime,

\[
 5<p,\quad p\ne239,317,quad d_N<2p,quad p\le d_N,           \tag{18}
\]

then

\[
       v_p(\operatorname{den}R_{N+1})=1.                     \tag{19}
\]

Its current source SHA-256 is
`cbe303cf13da7c60e2c4d602ba97b009a59c3cf49659b2e37d41165a02ab8f3a`.
T48 is registered in the repository axiom audit; the completed full gate
allows only `propext`, `Classical.choice`, and `Quot.sound`.

Take \(x=d_N\) in (12).  For every sufficiently large \(N\), choose

\[
                  p_N\in\mathcal P,qquad d_N/2<p_N\le d_N.  \tag{20}
\]

The prime is eventually larger than the two fixed exceptions, so (18)--(19)
apply.  Combining (16) and (19), for every \(m\ge0\),

\[
 \begin{aligned}
 v_{p_N}(10^m-16)&=0,\\
 v_{p_N}(R_{N+1})&=-1,\\
 v_{p_N}((10^m-16)R_{N+1})&=-1.                             \tag{21}
 \end{aligned}

Thus \((10^m-16)R_{N+1}\notin\mathbb Z\).  If instead
\((10^m-16)M_{N+1}\) were an integer, multiplying it by \(10^{N+1}\)
would make \((10^m-16)R_{N+1}\) an integer, contradicting (21).  This proves
(2), with \(j=N+1\).

The quantifiers are worth emphasizing:

\[
 \exists J\ \forall j\ge J\ \forall m\ge0:
              (10^m-16)M_j\notin\mathbb Z.                   \tag{22}
\]

The bad prime may vary with \(j\), but after it is selected it excludes
**all** exponents \(m\), not merely a bounded search range.

## 4. Exact finite witness inside the real Machin window

The same prime \(p_0=5521\) gives a compact finite replay.  Take \(N=459\).
Then

\[
 d_N=12\cdot459+15=5523,qquad {d_N\over2}<5521\le d_N.      \tag{23}
\]

At \(K=3(N+1)=1380\), the base-5 prefix has odd linear denominators through
\(5523\), and the base-239 prefix through \(5525\).  Since \(2p_0>5525\),
the only denominator divisible by \(p_0\) in either prefix is \(p_0\) itself.
The corresponding Taylor index \((p_0-1)/2=2760\) is even.  Therefore the
residue of \(p_0R_{460}\) modulo \(p_0\) is exactly

\[
 10^{460}\left({16\over5}-{4\over239}\right)
 =10^{460}{3804\over1195}
 \equiv551\not\equiv0\pmod {5521}.                           \tag{24}
\]

All regular terms have zero residue modulo \(p_0\) after multiplication by
\(p_0\); they do not vanish as rational numbers.  Equation (24)
independently certifies \(v_{5521}(R_{460})=-1\), while (9) certifies that
\(5521\nmid10^m-16\) for every \(m\).  This is one finite instance of the
asymptotic theorem, not evidence used in place of Chebotarev.

## 5. What the theorem does and does not buy

The result strengthens the obstruction to one proposed route:

- taking the actual natural sampled Machin truncations;
- choosing decimal exponents after seeing their reduced denominators; and
- hoping for exact reduced-denominator divisibility in \(10^m-16\).

It also gives the exact non-Archimedean strengthening (21): one incompatible
prime survives to exponent one in every selected rational phase.

It does **not** give a fixed positive lower bound for the ordinary circle
distance in (4).  If a reduced rational has denominator \(B\), nonintegrality
alone gives only

\[
                  \|a/B\|_{\mathbb T}\ge {1\over B},         \tag{25}
\]

and the Machin denominators are enormous.  A residue can therefore be
nonzero at \(p_N\) while being very close to an integer in the real metric.
An attack on (4) still needs ordered CRT/numerator control.  Chebotarev
supplies a denominator obstruction, not that missing Archimedean ordering.

Nor does the theorem apply automatically to a signed identity whose depths
and argument denominators change with \(j\).  Such a family would need its
own prime-survival theorem before the same bad-prime mechanism could be used.

## 6. Checker and literature record

Companion exact replay:
[`machin_chebotarev_anchor_obstruction_check.py`](machin_chebotarev_anchor_obstruction_check.py).

The checker uses only exact integer arithmetic.  It verifies:

1. primality and the two modular splitting certificates (8)--(9);
2. the complete multiplicative orbit of \(10\) modulo \(5521\), confirming
   that it never contains \(16\);
3. the upper-half window (23) and localized actual-Machin residue (24);
4. the expected T48 theorem name, source pin, and target pin; and
5. a bounded enumeration of the sufficient bad-prime class as an
   `experiment` only.

The literature input is the standard Chebotarev asymptotic.  It was checked
against Jesse Thorner and Asif Zaman,
[*A unified and improved Chebotarev density theorem*](https://doi.org/10.2140/ant.2019.13.1039),
*Algebra & Number Theory* **13** (2019), 1039--1068.  Their introduction
states the unconditional asymptotic
\(\pi_C(x)\sim |C|\operatorname{Li}(x)/|G|\), and their results prove stronger
effective forms.  The official MSP PDF downloaded on 2026-08-12 has SHA-256
`2998c066c04706018052a98fd6cbf9986c14246541c21dbf7db07bb07209c863`.

Searches covered *Chebotarev completely split primes*, *Kummer power residue
primes*, and *effective Chebotarev density theorem*.  No Artin-conjecture or
GRH input is used.

## Bottom line

There is a positive-density Chebotarev class of primes that can never divide
any \(10^m-16\).  T48 forces one of those primes into the reduced denominator
of every sufficiently deep natural sampled Machin truncation.  Hence, quite
apart from the already known decimal-primary obstruction, exact fixed-sixteen
denominator synchronization for that entire all-depth family is impossible
for an independent odd-prime reason.  The nonzero selected rational phase
remains uncontrolled; no fixed return or V1 proof follows.
