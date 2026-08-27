# General fixed-seed prime-band attack

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's local question has no external source URL; none is
invented here.  
Route: the fixed Machin seed used in T48--T50 and in
[`fixed_modulus_attack.md`](fixed_modulus_attack.md).

## Outcome and status

There is no proof here that every finite decimal word occurs in \(\pi\).
That target remains a `conjecture`.

The useful result is a `proof sketch` of a much stronger denominator theorem
for the exact rational Machin seed.  If

\[
 d=12N+15,\qquad
 Y_N=10^{N+1}M_{3(N+1)},
\]

then the product of distinct nonbase primes in the reduced denominator of
\(Y_N\) has logarithm

\[
                         d-o(d).                    \tag{1}
\]

More precisely, choosing

\[
 R=\left\lfloor {\log d\over16\log\log d}\right\rfloor,
 \qquad B={d\over2R+1},                              \tag{2}
\]

every non-endpoint prime \(B<p\le d\) survives for all sufficiently large
\(d\); discarding endpoint primes costs only \(\exp(o(d))\).  This extends
T50's two bands to a number of bands
tending to infinity.  The proof is elementary local rational arithmetic plus
the prime number theorem; it does not use an irrationality measure for
\(\pi\).

This advance produces a much stronger supply of actual denominator primes,
but it does **not** select the actual numerator residue in that large modulus.
If all the new high-prime components are frozen, their complementary modulus
is in fact only subexponential; Section 5 explains why the older
large-complement separator cannot simply be repeated.  Therefore (1) is not
a cylinder hit, cancellation theorem, normality statement, or resolution of
the canonical target.

The exact \(r=3\) coefficient, its exceptions, and endpoint closure below
have subsequently been formalized in
[`T51T51MachinSeedThirdBandPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean)
and are `machine-checked`. The accompanying finite computation is an
`experiment`. The growing-\(R\) asymptotic assertion remains a
`proof sketch`.

## 1. Exact seed and band classification

Let

\[
 S_q(m)=\sum_{j=0}^{m}{(-1)^j\over(2j+1)q^{2j+1}}.
\]

The seed, before multiplying by the \(p\)-unit \(10^{N+1}\), is

\[
 {Y_N\over10^{N+1}}
 =\sum_{\substack{1\le u\le d\\u\text{ odd}}}
 {4(-1)^{(u-1)/2}(4\cdot239^u-5^u)
  \over u5^u239^u}
 -{4\over(d+2)239^{d+2}}.                           \tag{3}
\]

Fix \(r\ge1\) and a prime in the half-open band

\[
             {d\over2r+1}<p\le {d\over2r-1}.        \tag{4}
\]

Assume throughout that \(p>\max(5,2r+1)\) and \(p\ne239\).  The only common
odd exponents \(u\le d\) divisible by \(p\) are then

\[
                   p,3p,\ldots,(2r-1)p.             \tag{5}
\]

Indeed, divisibility writes \(u=ap\); oddness makes \(a\) odd, and (4)
gives \(a<2r+1\).  Conversely all the exponents in (5) are at most \(d\).

The assumption \(p>2r+1\) is harmless for the asymptotic argument below.
It removes the possibility that one of the displayed cofactors itself
contributes an extra \(p\).  All terms of (3) outside (5), apart from the
explicit endpoint, are \(p\)-integral.

## 2. Exact localized coefficient

Multiply (3) by \(p\).  At \(u=(2s-1)p\), Fermat's theorem and
\(p>2s-1\) give

\[
 {p\over u}\,{4(-1)^{(u-1)/2}(4\cdot239^u-5^u)
       \over5^u239^u}
 \equiv
 (-1)^{(p-1)/2}{4(-1)^{s-1}\over2s-1}
 \left({4\over5^{2s-1}}-{1\over239^{2s-1}}\right)
 \pmod p.                                           \tag{6}
\]

Thus the exact rational coefficient, independent of \(p,N\), is

\[
 \boxed{
 C_r=4\sum_{s=1}^{r}{(-1)^{s-1}\over2s-1}
       \left({4\over5^{2s-1}}-{1\over239^{2s-1}}\right).}       \tag{7}
\]

If \(p\nmid d+2\), the endpoint is regular, so

\[
 pY_N/10^{N+1}\equiv(-1)^{(p-1)/2}C_r\pmod p.       \tag{8}
\]

Here a rational whose denominator is prime to \(p\) is read in
\(\mathbb F_p\).  Consequently

\[
 p\nmid\operatorname{num}(C_r)
 \quad\Longrightarrow\quad v_p(Y_N)=-1,             \tag{9}
\]

and \(p\) occurs exactly once in the reduced denominator.  Conversely, under
the same hypotheses, \(p\mid\operatorname{num}(C_r)\) gives exact
cancellation of the order-\(-1\) part.  It need not imply that \(p\) divides
the reduced numerator; it says only that the denominator does not retain the
single available \(p\).

### Why \(C_r\ne0\)

The coefficient in (7) is the difference of the alternating Machin partial
sums through odd exponent \(2r-1\).  Its first positive term dominates the
alternating tail (separately for bases 5 and 239); equivalently the standard
alternating-series inequalities give

\[
                         0<C_r<4.                   \tag{10}
\]

The upper constant is intentionally crude.  Positivity is the point: the
integer used below to record the numerator factors is nonzero.  No
irrationality result for \(\pi\) is needed.  In particular, the published
bound \(\mu(\pi)<8\) is useful for the T36--T41 digit-code transfer but gives
no additional modular noncancellation here.

## 3. The third band \(d/7<p\le d/5\)

For \(r=3\), exact reduction of (7) gives

\[
 C_3={38279241713339684\over12184551018734375}
 ={2^2\cdot19\cdot37\cdot79\cdot48049\cdot3586217
   \over5^6\,239^5}.                                \tag{11}
\]

All five displayed odd factors are prime.  Hence, away from a singular
endpoint, every prime in the third band survives except possibly

\[
                   19,37,79,48049,3586217.           \tag{12}
\]

These are genuine exceptions, not merely factors too small to enter the
band.  For example the following exact pairs have \(5p\le d<7p\):

| \(p\) | \(N\) | \(d=12N+15\) |
|---:|---:|---:|
| 19 | 7 | 99 |
| 37 | 15 | 195 |
| 79 | 32 | 399 |
| 48049 | 20020 | 240255 |
| 3586217 | 1494256 | 17931087 |

For the first three rows, direct construction and reduction of the complete
rational seed confirms that \(p\) is absent from its denominator.  This
finite confirmation is an `experiment`; equation (11) and the local
deduction (9) are the exact proof calculation.

## 4. Endpoint classification and the r=3 repair

The extra base-239 term in (3) matters precisely when \(p\mid d+2\).  Write

\[
                         d+2=ap.                    \tag{13}
\]

Because \(d+2\) and \(p\) are odd, \(a\) is odd.  The band inequalities
and \(p>d/(2r+1)\) imply \(a\le2r+1\).  Since \(d\ge(2r-1)p\), while
\(d+2=ap\), one has \(a>2r-1\) once \(p>2\).  Therefore

\[
                         d+2=(2r+1)p.               \tag{14}
\]

Reducing the endpoint together with (7) yields

\[
 E_r=C_r-{4(-1)^r\over(2r+1)239^{2r+1}},qquad
 pY_N/10^{N+1}\equiv(-1)^{(p-1)/2}E_r\pmod p.       \tag{15}
\]

For \(r=3\), (14) says \(d+2=7p\).  As \(d+2=12N+17\equiv5\pmod{12}\),
this forces \(p\equiv11\pmod{12}\).  Direct reduction gives

\[
 E_3={15305839961353732690848\over4871956171187883640625}
 ={2^5 3^2 13\,29\,8429\,35533\,470668789
   \over7\,5^6 239^7}.                              \tag{16}
\]

None of its odd numerator primes is \(11\pmod{12}\).  Thus an r=3 endpoint
prime can never divide the numerator in (16).  Combining (11)--(16) gives
the clean finite statement:

> If \(p>7\) is prime, \(p\ne239\), and
> \(5p\le12N+15<7p\), then
> \(v_p(Y_N)=-1\) unless
> \(p\in\{19,37,79,48049,3586217\}\).

No separate endpoint hypothesis is required in that r=3 statement. T51
machine-checks this exact statement, its coefficient factorizations, and
reduced-denominator multiplicity one.

This simplification does **not** persist for all \(r\).  The first explicit
counterexample is

\[
 N=43,\quad d+2=533=13\cdot41,\quad r=6,\quad
 41\mid\operatorname{num}(E_6).                    \tag{17}
\]

The complete reduced rational seed indeed loses its factor 41.  Any general
theorem that simply declares endpoints harmless is false.

## 5. Asymptotic survival through growing bands

This section is a `proof sketch`; it records each quantitative loss so that
the asymptotic assertion (1) is inspectable.

Let \(R=R(d)\) be as in (2), ignoring finitely many small \(d\), and set

\[
 H_R=(2R-1)!\,5^{2R-1}239^{2R-1}.                  \tag{18}
\]

For every \(r\le R\), \(H_R C_r\) is an integer: the factorial clears all
odd cofactors \(2s-1\), and the two powers clear the base denominators.
By (10), it is a nonzero integer with

\[
 \log|H_R C_r|=O(\log H_R)=O(R\log R).              \tag{19}
\]

In fact the chosen \(R\) gives the sharper pointwise conclusion

\[
                    4H_R<B                         \tag{19a}
\]

for all sufficiently large \(d\): Stirling gives
\(\log H_R=(1/8+o(1))\log d\), whereas
\(\log B=(1-o(1))\log d\).  Since (10) implies
\(0<H_RC_r<4H_R\), **no** non-endpoint prime \(p>B\) can divide
\(H_RC_r\).  Thus every such prime survives, rather than merely all but an
exceptional product of logarithmic weight (20).  The height-sum argument
below is retained as a robust weaker accounting and works for less sharply
tuned choices of \(R\).

For a non-endpoint prime \(p>B=d/(2R+1)\), exactly one of the bands
\(1\le r\le R\) applies.  If it does not survive, then it divides
\(\operatorname{num}(C_r)\), hence it divides \(H_RC_r\).  Distinct failed
primes therefore have total logarithmic weight at most

\[
 \sum_{r\le R}\log|H_RC_r|=O(R^2\log R)=o(d).       \tag{20}
\]

Primes with \(p\le2R+1\), or \(p=5,239\), already lie below \(B\) for
large \(d\).  Endpoint primes can simply be discarded: each divides the
single integer \(d+2\), so their total distinct-prime logarithmic weight is
at most

\[
             \sum_{p\mid d+2}\log p\le\log(d+2)=o(d).            \tag{21}
\]

The prime number theorem in Chebyshev form now gives

\[
 \sum_{B<p\le d}\log p
   =\vartheta(d)-\vartheta(B)=d-o(d),               \tag{22}
\]

because \(B=o(d)\).  Removing (20), (21), and the fixed base exceptions
proves (1).

### Multiplicities and the residual cofactor

Every nonbase prime factor of the full seed denominator comes from an odd
linear denominator at most \(d+2\).  Its exponent is at most
\(\lfloor\log_p(d+2)\rfloor\).  Consequently the total logarithmic
multiplicity that can be contributed by primes \(p\le B\) is at most

\[
 \sum_{p\le B}\left\lfloor{\log(d+2)\over\log p}\right\rfloor\log p
 \le \pi(B)\log(d+2)=O(B)=o(d),                    \tag{23}
\]

where the last estimate uses \(\log B\sim\log d\) for (2) and the prime
number theorem (a Chebyshev bound would also suffice with the same scale).
For \(p>B\), (4) ensures \(p^2>d+2\) for all sufficiently large \(d\), so
their odd-linear multiplicity is one.  The local conclusion (9) then gives
the reduced-denominator exponent exactly one, not just divisibility.  Thus
prime powers do not hide a linear-size remainder behind the radical estimate.

Equation (23) should be read carefully: it bounds the small-prime
multiplicity contribution.  Failed or discarded large primes have already
been charged separately in (20)--(21); combining unlike losses without this
separation would be circular.

This also audits the stronger complementary-factor formulation used in the
same-modulus attack.  Let \(Q_N\) be the actual reduced denominator.  Put into
\(F_N\) the **complete** 5- and 239-primary powers and every surviving
high prime \(p>B\), once; the local valuation calculation gives its exact
exponent one.  Endpoint high primes not included in \(F_N\) contribute at
most the \(O(\log d)\) weight in (21), while all remaining factors of
\(D_N=Q_N/F_N\) are small-prime powers.  Equations (21) and (23) give

\[
                         \log D_N=o(d).             \tag{24}
\]

So freezing all the nearly-full high-prime radical leaves only a
subexponential complementary modulus.  This corrects the direction of the
older separator: once the new general survivor set itself is frozen, that
particular Kanold alternative-numerator construction no longer has a large
complement to vary.  It still does not prove anything about the actual
numerator; it shows that the next step must exploit its global congruences,
not merely repeat the same large-complement separator.

## 6. Exact falsification checks

[`general_seed_band_check.py`](general_seed_band_check.py) performs exact
integer/Fraction checks and pins the target hash.  Its retained run was:

```text
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
C3=38279241713339684/12184551018734375
E3=15305839961353732690848/4871956171187883640625
full_seed_rows=10098 endpoint_rows=41 predicted_nonsurvivors=152 mismatches=0
endpoint_scan_rows=2731 endpoint_bad=[(43, 41, 6, 13), (337, 131, 15, 31), (1352, 149, 54, 109), (1380, 137, 60, 121), (2157, 439, 29, 59), (2194, 479, 27, 55), (3513, 233, 90, 181)]
```

The 10,098-row check constructs and reduces every full seed for
\(0\le N\le100\), classifies every eligible prime, and compares actual
denominator survival with the exact \(C_r/E_r\) residue criterion.  The
2,731-row endpoint scan covers \(0\le N\le5000\) using exact modular
arithmetic and finds seven cancellations, including (17).  These finite
results are labeled only `experiment`.

Reproduction:

```bash
python3 work/ultrapi-resume/general_seed_band_check.py
```

## 7. What this does and does not buy

The new denominator theorem is genuine structural progress on the Machin
route. T48, T50, and T51 prove the first three fixed bands in Lean; the
calculation above shows that their mechanism scales through \(R\to\infty\)
and captures essentially every prime up to \(d\). A possible further formal
task is a reusable finite-\(R\) band lemma.

It also closes off a tempting but incorrect hope: a still larger denominator
alone will not force the actual orbit into every decimal cylinder.  The
same-modulus construction can choose many alternative coprime numerators with
the same controlled local components.  The unresolved phase remains a theorem
about the **actual complementary numerator residue**, or an independent
archimedean cancellation/distribution theorem.  Neither an irrationality
measure nor the nearly full denominator radical supplies that phase.

Final claim labels:

- canonical every-word statement for \(\pi\): `conjecture`;
- T48--T51 statements cited as such in their own audited modules:
  `machine-checked`;
- exact \(r=3\) coefficient, endpoint closure, valuation, and denominator
  multiplicity: `machine-checked` in T51;
- general coefficient identity and growing-band asymptotic survival:
  `proof sketch`;
- retained finite seed and endpoint scans: `experiment`.
