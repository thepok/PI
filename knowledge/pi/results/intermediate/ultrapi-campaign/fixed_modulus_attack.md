# Fixed-modulus attack on the actual Machin pulse

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: the immutable local root records Marcel's 2026-07-21 question;
there is no external source URL to preserve or invent.  
Route: equations (11af)--(11ap) of [`ultrapi.md`](../../ultrapi.md), T36,
T38, and T44--T50. This report's original controlled set is deliberately the
at-most-three fresh T45 primes; the four-class repair is in
[`multiprime_adversarial.md`](multiprime_adversarial.md).

## Outcome and claim status

There is no complete proof here that every finite decimal word occurs in
\(\pi\). The canonical target remains a `conjecture`.

The main new finding is a precise obstruction to the current
fixed-composite-modulus strategy. Even after one fixes

1. the **actual reduced denominator** \(Q_N\) of the pulse seed,
2. the seed's complete \(5\)-primary and \(239\)-primary numerator
   components, and
3. every numerator component in the at-most-three-element fresh set
   \(\mathcal F_N\) born from \(\Delta_N\),

there are, for all sufficiently large \(N\), other reduced numerators at the
same \(Q_N\) with exactly those components and whose fractional parts have
an all-5 prefix of length \(2N+2\). Their length-\(2N+2\), frequency-one exponential sum has
size at least

\[
 \cos(\pi/10)(2N+2).
\]

This is a `proof sketch`, not a separator for the **actual** Machin
numerator. It rigorously identifies what the route still has to use: the
actual residue in the large complementary cofactor. Denominator size,
5-/239-adic data, every fresh-prime pulse, and their complete fixed CRT
components do not imply cancellation, even jointly.

The exact experiment through \(1\le N\le300\) has zero component and
prime-survival failures and also satisfies the separator's crude sufficient
inequality at every tested row. This remains an `experiment`; the asymptotic
argument is the separately labeled `proof sketch` below.

## 1. Normalized target and quantifiers

The canonical V1 statement is

\[
 \forall L\in\mathbb N\;\forall w\in\{0,\ldots,9\}^{L}\;
 \exists j\in\mathbb N:\quad
 (d_j(\pi),\ldots,d_{j+L-1}(\pi))=w,
\]

where \(d_j(\pi)\) are the digits after the decimal point and leading zeroes
in \(w\) are permitted. The length-zero case is vacuous. This is finite,
contiguous occurrence; it is not the false claim about all infinite words
and not the subsequence variant. The original phrase "any integer sequence"
has those three ambiguous readings, already frozen in the immutable root.

## 2. Exact reduced pulse seed

For \(q>1\) and \(m\ge0\), put

\[
 S_q(m):=\sum_{j=0}^{m}\frac{(-1)^j}{(2j+1)q^{2j+1}}.
\]

Take \(n=N+1\), and write

\[
 d:=12n+3=12N+15.
\]

T36's rational seed at the start of the T45 pulse is exactly

\[
 \boxed{
 Y_N:=y_{N+1}=10^nM_{3n}
 =10^n\bigl(16S_5(6n+1)-4S_{239}(6n+2)\bigr)
 ={a_N\over Q_N}, }
 \tag{1}
\]

with \(Q_N>0\) and \(\gcd(a_N,Q_N)=1\). This is the reduced seed requested
by the fixed-modulus formulation; no varying modulus occurs when (1) is
multiplied by powers of ten.

Combining the two summands at every common odd exponent \(u\le d\) gives the
more revealing exact expression

\[
 {Y_N\over10^n}
 =\sum_{\substack{1\le u\le d\\u\text{ odd}}}
 {4(-1)^{(u-1)/2}(4\cdot239^u-5^u)
  \over u5^u239^u}
 -{4\over(d+2)239^{d+2}}.                         \tag{2}
\]

Thus \(a_N,Q_N\) can be obtained without any value of \(\pi\): reduce the
finite rational number in (2). Equivalently, take the LCD of the individually
reduced terms in (2), clear it to an integer numerator, and divide both by
their gcd. This is an exact finite formula, not an asymptotic presentation.

### The 5- and 239-primary components

For later auditing it is useful to reverse either Taylor sum. Define

\[
 R_q(m):=(-1)^m(2m+1)q^{2m+1}S_q(m).
\]

Directly separating the last term gives the exact recurrence

\[
 R_q(m)=1-q^2{2m+1\over2m-1}R_q(m-1),\qquad R_q(0)=1. \tag{3}
\]

Consequently the individual Machin blocks have exact valuations

\[
\begin{aligned}
 v_5(16\,10^nS_5(6n+1))
   &=n+v_5(R_5(6n+1))-d-v_5(d),\\
 v_{239}(-4\,10^nS_{239}(6n+2))
   &=v_{239}(R_{239}(6n+2))-(d+2)-v_{239}(d+2).
\end{aligned}                                                   \tag{4}
\]

Reducing (1) defines the exact exponents

\[
 s_N:=v_5(Q_N),\qquad r_N:=v_{239}(Q_N).            \tag{5}
\]

The exact run through \(N=300\) found that (4)'s relevant block always has
strictly smaller valuation than the opposite-base block, and hence

\[
\begin{aligned}
 s_N&=d+v_5(d)-n-v_5(R_5(6n+1)),\\
 r_N&=d+2+v_{239}(d+2)-v_{239}(R_{239}(6n+2)).
\end{aligned}                                                   \tag{6}
\]

Equation (6) outside the checked range is recorded only as a `conjecture` in
this report. In particular, the tempting simplification
\(v_5(R_5(6n+1))=0\) is false: the exact recurrence already has positive and
negative exceptional valuations. The separator below does **not** assume
(6), or any lower bound for \(s_N\) or \(r_N\).

### T45 fresh-prime components

Let

\[
 \mathcal F_N:=\{p=12N+5+2k:\ k\in\{1,3,4\},\ p>12
   \text{ prime},\ p\ne239\}.
\]

T45 machine-checks \(v_p(\Delta_N)=-1\) for every
\(p\in\mathcal F_N\). Every denominator in \(y_N\) has odd linear factor
strictly below \(p\), so \(y_N\) is \(p\)-integral. The unequal-valuation
sum in \(y_{N+1}=10y_N+\Delta_N\) therefore gives, at `proof sketch`
status,

\[
 v_p(Y_N)=-1\qquad(p\in\mathcal F_N).               \tag{7}
\]

In particular, each such \(p\) occurs exactly once in \(Q_N\), and its
nonzero numerator component is the T45 residue transported into (1).

Define the full currently controlled factor and its complementary cofactor
by

\[
 F_N:=5^{s_N}239^{r_N}\prod_{p\in\mathcal F_N}p,
 \qquad D_N:=Q_N/F_N.                                \tag{8}
\]

Equations (5), (7), and reducedness give
\(\gcd(F_N,D_N)=1\). Fixing \(a_N\bmod F_N\) fixes at once the complete
5-primary, 239-primary, and all components in the at-most-three-element
fresh set \(\mathcal F_N\) of the seed at
the same reduced modulus \(Q_N\).

## 3. Many other actual denominator primes survive

The key fact missed by the first prime-pulse analysis is that \(D_N\) is
itself exponentially large for a route-specific reason.

### Upper-half prime survival (`machine-checked`)

Let \(\ell\) be prime with

\[
 d/2<\ell\le d,\qquad \ell\notin\{239,317\}.        \tag{9}
\]

Among all odd linear denominators in (2), only the term \(u=\ell\) is
divisible by \(\ell\). Multiplying that term by \(\ell\) and using Fermat
gives the nonzero residue

\[
 {4(-1)^{(\ell-1)/2}(4\cdot239^\ell-5^\ell)
   \over5^\ell239^\ell}
 \equiv
 {4(-1)^{(\ell-1)/2}\,951\over5\cdot239}\not\equiv0\pmod\ell. \tag{10}
\]

The only prime factors of \(951\) are 3 and 317. All other terms are
\(\ell\)-integral. Hence

\[
 \boxed{v_\ell(Y_N)=-1}                              \tag{11}
\]

for every \(\ell\) in (9). This exact statement, including the endpoint
exclusion and the reduced-denominator corollary, is machine-checked in
[`T48T48MachinSeedUpperHalfPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T48T48MachinSeedUpperHalfPrimeSurvival.lean).
It is the full-seed analogue of T45's local noncancellation and uses the
actual Machin coefficient ratio, not a loose product grid. In fact the
endpoint is excluded for every relevant \(N\): \(d+2<3\ell\), while the only
possible positive multiples \(\ell\) and \(2\ell\) are ruled out respectively
by \(d+2>d\ge\ell\) and the odd parity of \(d+2\).

At most three primes in (9) lie in \(\mathcal F_N\). Therefore (11) implies

\[
 \log D_N\ge
 \vartheta(d)-\vartheta(d/2)-O(\log d),              \tag{12}
\]

where the omitted factors are only 239, 317, and the at most three fresh
primes. The prime number theorem in Chebyshev form gives

\[
 \log D_N\ge {d\over2}+o(d)=6N+o(N).                 \tag{13}
\]

Every prime factor of \(Q_N\) comes from 5, 239, or an odd linear
denominator at most \(d+2\), so

\[
 \omega(D_N)\le\pi(d+2)=o(d).                        \tag{14}
\]

## 4. Same-modulus, same-component, maximally noncancelling seeds

Let \(J(D)\) be the least length such that every arithmetic progression of
that length and step coprime to \(D\) contains a term coprime to \(D\).
Kanold's theorem gives (and coprimality also makes
\(J(D)=J(\operatorname{rad}D)\))

\[
 J(D)\le2^{\omega(D)}.                               \tag{15}
\]

Consider all numerators

\[
 a_j=a_N+F_Nj\pmod {Q_N},\qquad j\pmod {D_N}.        \tag{16}
\]

They retain \(a_N\bmod F_N\), so every component listed in (8) is exactly
unchanged. This means the components currently extracted by T44/T45, not
every component one could derive from the upper-half calculation.

For the coprimality filter, multiply (16) modulo \(D_N\) by
\(F_N^{-1}\). It becomes a run of consecutive residues
\(F_N^{-1}a_N+j\). Thus Kanold applies literally: every \(J(D_N)\)
consecutive choices contain a numerator coprime to \(D_N\). Reducedness
modulo \(F_N\) was already inherited from \(a_N\), so consecutive reduced
fractions \(a_j/Q_N\) selected from (16) have cyclic gaps at most

\[
 {J(D_N)\over D_N}\le{2^{\omega(D_N)}\over D_N}.    \tag{17}
\]

Combining (13)--(15),

\[
 \log {D_N\over2^{\omega(D_N)}}
 \ge6N+o(N).                                         \tag{18}
\]

Let \(L_N=2N+2\), the maximum T45 pulse length. Since

\[
 6>2\log10=4.60517\ldots,
\]

(18) yields, for every sufficiently large \(N\),

\[
 {J(D_N)\over D_N}<10^{-L_N}.                        \tag{19}
\]

Thus (16) contains a reduced numerator \(a'_N\) at the **same** denominator
\(Q_N\), with the **same** residue modulo \(F_N\), in every length-\(L_N\)
decimal cylinder. Choose the cylinder with word \(55\ldots5\). Then

\[
 \left\{10^t{a'_N\over Q_N}\right\}\in[0.5,0.6)
 \qquad(0\le t<L_N).                                 \tag{20}
\]

For \(e(x)=\exp(2\pi i x)\), projecting the phases in (20) onto the
direction \(e(0.55)\) gives

\[
 \boxed{
 \left|\sum_{t=0}^{L_N-1}e\!\left({a'_N10^t\over Q_N}\right)\right|
 \ge L_N\cos(\pi/10).}                               \tag{21}
\]

This is essentially maximal, rather than cancelling. It remains true while
preserving all of the actual components in (8).

### Exact interpretation of the obstruction

Equation (21) rules out a bound uniform over numerators specified only by
the denominator and the 5-, 239-, and fresh-prime components. It also rules
out combining separate cancellation estimates for just those projections:
their joint data admit almost maximally aligned full phases.

It does **not** say that the actual \(a_N\) has the avoiding prefix. The
actual residue \(a_N\bmod D_N\) picks one point from this exponentially rich
family, and the argument deliberately varies that residue. A theorem for

\[
 \sum_{t<T}e_{Q_N}(ha_N10^t),\qquad T\asymp N,        \tag{22}
\]

using the specific full \(a_N\) would still be genuine progress. The
present result says precisely that its proof cannot discard or average away
the \(D_N\)-component.

## 5. Exact falsification run (`experiment`)

The reproducible program is
[`fixed_modulus_attack_experiment.py`](fixed_modulus_attack_experiment.py),
SHA-256
`e9e006d3f92881be9b144551a6183f89a4ced0db7d1ed355bf838e9464706906`.
It uses Python `Fraction`, integer powers, and an elementary sieve. No
floating-point value or digit table of \(\pi\) enters the calculation.

Command:

```bash
python work/ultrapi-resume/fixed_modulus_attack_experiment.py --max-n 300
```

Retained output:

```text
rows=300
failures=0
first=N=1, D_bits=23, omega(D)=6, L=4
last=N=300, D_bits=5172, omega(D)=501, L=602
all exact component, upper-half-prime, and separator checks passed
```

For every \(1\le N\le300\), it checked exactly:

- the reduced rational seed (1);
- both directly constructed reverse quantities and the component equalities
  (6);
- exponent one for every prime in \(\mathcal F_N\);
- exponent one for every upper-half prime in (9);
- \(\gcd(F_N,D_N)=1\); and
- the stronger finite sufficient inequality
  \(D_N>2^{\omega(D_N)}10^{2N+2}\).

The script does not construct the avoiding numerator or replay its digits;
the last inequality is sufficient to make the Kanold/CRT separator effective
at every tested row, not merely asymptotically. Finite verification has zero proof leverage
for untested \(N\); it falsifies sign, endpoint, cancellation, and scale
mistakes in the `proof sketch`.

## 6. Primary-source search (`literature-checked`)

Search date: **2026-08-12 UTC**. The relevant primary sources were checked
against the exact hypotheses above.

- H.-J. Kanold,
  [*Über eine zahlentheoretische Funktion von Jacobsthal*](https://eudml.org/doc/161543),
  Math. Ann. 170 (1967), 314--326, supplies the classical
  \(J(D)\le2^{\omega(D)}\) bound used in (15).
- Broadbent--Kadiri--Lumley--Ng--Wilk,
  [*Sharper Bounds for the Chebyshev function*](https://arxiv.org/abs/2002.11068),
  supplies explicit primary-source bounds much stronger than the
  \(\vartheta(x)=x+o(x)\) input used in (12)--(13).
- Kerr,
  [*Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170),
  treats pure prime-modulus sums. Its nontrivial ranges are polynomial in
  the modulus/order, not \(T\asymp\log Q_N\), and it does not retain the
  cofactor component exposed here.
- Bourgain--Chang,
  [*Exponential sum estimates over subgroups and almost subgroups of
  \(\mathbb Z_q^*\)*](https://math.ucr.edu/~mcc/paper/122%20NewExp.pdf),
  requires a unit base, polynomial-length orbit, and large local orders.
  Base 10 is nonunit on \(5^{s_N}\), and (22) is logarithmic length.
- Bailey--Crandall,
  [*Random Generators and Normal Numbers*](https://www.davidhbailey.com/dhbpapers/bcnormal.pdf),
  records the coprime Korobov--Niederreiter route and a
  square-root-modulus discrepancy scale; neither applies to (22).

Additional searches for incomplete geometric sums modulo prime powers,
nonunit composite bases, and p-adic exponential sums found complete-family
or polynomial-length results, not a theorem for the selected logarithmic
segment (22). This is a bounded negative search finding, not a claim that no
such theorem exists.

## 7. Remaining fixed-pi bridge

T46 now gives the `machine-checked` exact shadowing identity

\[
 y_{N+1+t}=10^tY_N+R_{N+1,t},\qquad
 0\le R_{N+1,t}<10^t\left({10\over625^3}\right)^{N+1}.
\]

It also proves the fixed-initial-denominator rational representation and the
uniform full-pulse error bound; its import and axiom-audit registration are
present. It does not prove cancellation. Cancellation for (22), uniformly
over the finitely many frequencies
needed for a fixed decimal cylinder, would transfer over the full pulse with
exponentially small error. T48 machine-checks the local upper-half
denominator-survival input to the cofactor estimate. The new separator shows that none of the now
known component data can provide that cancellation uniformly. The surviving
task is a theorem about the specific full cofactor residue
\(a_N\bmod D_N\), or a genuinely different fixed-\(\pi\) mechanism.

## Bottom line

The fixed-modulus correction remains real progress: an entire T45 pulse is
one rational powers-of-ten orbit plus a tiny error. But its modulus has a
large complementary factor carrying enough unresolved residue information
to encode the whole pulse's decimal itinerary, even after every currently
controlled local component is frozen. The exact Machin numerator chooses
one itinerary; no searched theorem controls that choice. V1 remains a
`conjecture`.
