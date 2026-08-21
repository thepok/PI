# Simultaneous Machin prime pulses: scale, CRT collapse, and separator

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Inputs: T38, T45, equations (11af)--(11ai) of
[`ultrapi.md`](../../ultrapi.md), and
[`machin_recurrence_report.md`](machin_recurrence_report.md). The separator
extends, rather than replaces, the stronger same-denominator construction in
[`fixed_modulus_attack.md`](fixed_modulus_attack.md).

## Claim status and outcome

The target remains a `conjecture`. There is no proof here that every finite
decimal word occurs in \(\pi\).

### Adversarial correction after T47

Sections 1--4 below originally use the explicitly defined **T45 interior**
set \(S_{j,L}\). Their formulas and separator are valid at that scope. They
must not be read as freezing every pulse now derivable from T47: consecutive
right- and left-endpoint forcings create an additional class
\(5\pmod {12}\) pulse. Consequently, the original phrases “all simultaneous
prime components” and “all overlapping prime pulses” were too broad and are
withdrawn at that point in the argument. The corrected four-class analysis
and two-band cofactor repair are now recorded in
[`multiprime_adversarial.md`](multiprime_adversarial.md). T49 and T50
machine-check its load-bearing local arithmetic; its PNT/Kanold separator
layer remains a `proof sketch`. The established claim in Sections 1--4 below
is still the narrower all-**T45-interior** separator. No claim about V1
depends on the overbroad wording.

The T45 prime-survival theorem used below is `machine-checked`. The long-pulse
propagation and the deductions made from it below are `proof sketch`: their
integer and CRT steps are written out, but they are not Lean declarations.
Finite calculations are labelled `experiment`. The source search and use of
the prime number theorem in arithmetic progressions are labelled
`literature-checked` as of the audit date.

The main finding is negative but structural:

1. At one time \(j\), about \(6j/\log j\) T45 primes are simultaneously
   active and their product is \(\exp((6+o(1))j)\). On a common pulse block
   of length \(L\sim\lambda j\), the product is
   \(\exp(((6-3\lambda)+o(1))j)\).
2. These components are **not independent coordinates**. Their signs are a
   fixed Dirichlet character, and CRT collapses the whole vector to one
   rational seed followed by multiplication by 10.
3. Even at the **actual reduced denominator**, fixing its complete 5- and
   239-primary components and all simultaneous T45-interior components leaves an
   explicit CRT family of reduced numerators that can prescribe an avoiding
   decimal prefix. The same exact T38 forcing can then be added without
   destroying either the active pulses or the avoidance.

Consequently, accumulating T45 primes does not by itself bridge to an
archimedean decimal hit. A successful argument must control the actual
Machin seed's complementary CRT component, not merely more prime
projections.

## Normalized target and ambiguities

The canonical target V1 is

\[
 \forall m\ge0\;\forall a<10^m\;\exists n\ge0:\qquad
 \left\lfloor10^m\{10^n\pi\}\right\rfloor=a.
\]

This includes words with leading zeroes. The source records two distinct
readings that are not substituted here: V2 asks for every infinite word as a
contiguous tail and is false; V3 asks for every infinite word as a
subsequence and is equivalent to every digit occurring infinitely often,
which is open. All quantifiers below concern only the rational Machin orbit
used as a route toward V1.

## 1. Exact geometry of overlapping pulses

Put

\[
 y_n:=10^nM_{3n},\qquad
 y_{n+1}=10y_n+\Delta_n.
\]

For an admissible T45 prime, write

\[
 p=12N+5+2k,\qquad k\in\{1,3,4\},\qquad p\ne239.
\]

The reviewed pulse calculation gives, at `proof sketch` status,

\[
 py_{N+1+t}\equiv
 4(-1)^k\frac{951}{5\cdot239}\,10^{N+1+t}\pmod p. \tag{1}
\]

The range is \(0\le t\le2N\) for \(k=1\), and
\(0\le t\le2N+1\) for \(k=3,4\). Here a congruence for a
\(p\)-integral rational has its usual localization meaning.

For a block of integer times

\[
 I_{j,L}:=\{j,j+1,\ldots,j+L-1\},
\]

the pulses active throughout the whole block are exactly the primes from the
following three sets, apart from the excluded prime 239:

\[
\begin{array}{c|c|c}
 k&p&N\text{ range}\\ \hline
 1&12N+7&\left\lceil\dfrac{j+L-2}{3}\right\rceil\le N\le j-1,\\[2mm]
 3&12N+11&\left\lceil\dfrac{j+L-3}{3}\right\rceil\le N\le j-1,\\[2mm]
 4&12N+13&\left\lceil\dfrac{j+L-3}{3}\right\rceil\le N\le j-1.
\end{array} \tag{2}
\]

This is just the start condition \(N+1\le j\) together with the appropriate
pulse endpoint. In particular, at a single time the active primes occupy
three residue classes and an interval of scale

\[
 p\in[4j+O(1),12j+O(1)],\qquad
 p\equiv1,7,11\pmod {12}. \tag{3}
\]

## 2. How many components, and how large is their product?

Status: application at `proof sketch` status of a
`literature-checked` standard theorem.

For a reduced residue class \(a\pmod {12}\), the prime number theorem in
arithmetic progressions says

\[
 \vartheta(x;12,a):=
 \sum_{\substack{p\le x\\p\equiv a\ (12)}}\log p
 =\frac{x}{4}+o(x). \tag{4}
\]

This fixed-modulus result is also covered by the explicit estimates of
[Ramaré--Rumely, *Primes in arithmetic progressions*](https://ramare-olivier.github.io/Maths/rumely.pdf).
Let \(L=\lfloor\lambda j\rfloor\), with fixed \(0\le\lambda<2\), and let
\(S_{j,L}\) be the primes in (2). Applying (4) to the three endpoint
intervals gives

\[
 \boxed{\#S_{j,L}\sim(6-3\lambda)\frac{j}{\log j}},\qquad
 \boxed{\log\!\prod_{p\in S_{j,L}}p
       =(6-3\lambda)j+o(j).} \tag{5}
\]

Thus one time has product \(\exp((6+o(1))j)\), while a common block of
length \(j/2\) has product \(\exp((4.5+o(1))j)\). If one multiplies every
eligible prime whose pulse has merely *started* by time \(j\), rather than
requiring it still to be active, the logarithm is \(9j+o(j)\). Those older
components no longer obey one uninterrupted geometric law, so this larger
number is not available for the present pulse argument.

For comparison, a natural common denominator for \(y_j=10^jM_{3j}\) is

\[
 \mathcal D_j=
 5^{11j+3}239^{12j+5}
 \operatorname{lcm}\{r\le12j+5:r\text{ odd}\}. \tag{6}
\]

Indeed, the last base-5 exponent is \(12j+3\), the last base-239 exponent
is \(12j+5\), and decimal scaling cancels \(j\) powers of 5 from the
base-5 component. The prime number theorem gives

\[
 \log\mathcal D_j=
 \bigl(11\log5+12\log239+12\bigr)j+o(j)
 =95.4213796599\ldots j+o(j). \tag{7}
\]

The base-power part alone has logarithmic coefficient

\[
 11\log5+12\log239=83.4213796599\ldots. \tag{8}
\]

The asymptotic logarithmic proportions are therefore:

| prime information | versus base powers | versus the natural common denominator |
|---|---:|---:|
| active at one time, coefficient 6 | 7.1924% | 6.2879% |
| active for a block of length \(j/2\), coefficient 4.5 | 5.3943% | 4.7159% |
| every pulse born by time \(j\), coefficient 9 | 10.7886% | 9.4318% |

These ratios are diagnostic, not a theorem that a small logarithmic share is
automatically useless. The CRT collapse and separator below provide the
actual insufficiency argument.

## 3. All simultaneous residues collapse to one coordinate

Status: `proof sketch`.

Let \(\chi_4\) be the nontrivial character modulo 4. The three slot signs in
(1) satisfy

\[
 (-1)^k=\chi_4(p):
 \quad k=4\Longleftrightarrow p\equiv1\pmod {12},
 \quad k=1,3\Longleftrightarrow p\equiv7,11\pmod {12}. \tag{9}
\]

Fix a common active set \(S=S_{j,L}\), put

\[
 P:=\prod_{p\in S}p,qquad
 B_S:=\sum_{p\in S}\chi_4(p)\frac{P}{p}. \tag{10}
\]

For every \(p\mid P\), reduction of (10) gives

\[
 B_S(P/p)^{-1}\equiv\chi_4(p)\pmod p. \tag{11}
\]

Let \(A_j\pmod P\) be defined by

\[
 A_j\equiv3804\cdot1195^{-1}\cdot10^jB_S\pmod P, \tag{12}
\]

where \(3804=4\cdot951\), \(1195=5\cdot239\), and the inverse exists because
all primes in \(S\) exceed 12 and differ from 239. Equations (1) and (11)
show that the full vector of \(p\)-components is represented by the **single**
rational

\[
 \alpha_j:=\frac{A_j}{P}. \tag{13}
\]

Moreover \(A_j\) is coprime to \(P\), and throughout the common pulse block
the vector at time \(j+t\) is represented by

\[
 \frac{10^tA_j}{P}\pmod1. \tag{14}
\]

Thus the putative many-prime Fourier factor is exactly

\[
 \sum_{0\le t<T}e_P(hA_j10^t), \tag{15}
\]

one lacunary powers-of-10 orbit modulo a squarefree composite. It is not a
tensor product of independently sampled prime orbits. The signed reciprocal
numerator \(B_S\) is special, but no estimate controlling (15) at
\(T\asymp j\asymp\log P\) was found.

This also explains why applying a good prime-modulus estimate separately at
each factor is invalid: after CRT, all factors depend on the same one-dimensional
parameter \(10^t\), and the complementary factors act as correlated unit-modulus
weights.

## 4. Same actual denominator, all T45-interior active components, and an avoiding seed

Status: `proof sketch`.

The companion
[`fixed_modulus_attack.md`](fixed_modulus_attack.md) proves a stronger
separator than the freely enlarged \(5^s\)-grid considered in the first
version of this note: it keeps the **actual reduced denominator** and uses
upper-half prime survival plus Kanold's Jacobsthal bound. This section records
only the additional calculation needed to freeze *all overlapping active
T45-interior pulses*, not just the at most three primes born at the block
origin. T47's additional endpoint pulse is outside the set defined here.

Write the actual seed in lowest terms as

\[
 y_j=\frac{a_j}{Q_j},\qquad Q_j>0,\qquad(a_j,Q_j)=1,
\]

and put \(d_j=12j+3\). The upper-half argument in the companion report proves
at `proof sketch` status that every prime

\[
 \ell\in U_j:=\{\ell:d_j/2<\ell\le d_j\},
 \qquad \ell\notin\{239,317\},                 \tag{16}
\]

occurs exactly once in \(Q_j\). Let

\[
 s_j=v_5(Q_j),\qquad r_j=v_{239}(Q_j),
\]

and enlarge the controlled factor from the companion report to

\[
 F_{j,L}:=5^{s_j}239^{r_j}\prod_{p\in S_{j,L}}p,
 \qquad D_{j,L}:=Q_j/F_{j,L}.                    \tag{17}
\]

Every active pulse has \(v_p(y_j)=-1\), so (17) is a factorization with
\((F_{j,L},D_{j,L})=1\). Fixing \(a_j\pmod {F_{j,L}}\) fixes the complete
5-primary component, the complete 239-primary component, and **every** prime
component in (1) that persists across the block.

There are still enough upper-half primes outside the controlled set. Let
\(L=\lfloor\lambda j\rfloor\), \(0<\lambda<2\). The class
\(5\pmod {12}\) never occurs in \(S_{j,L}\), and contributes
\((3/2)j+o(j)\) to the logarithm of the product in (16). If
\(\lambda\le1/2\), that alone gives

\[
 \log D_{j,L}\ge\frac32j+o(j).                  \tag{18}
\]

If \(\lambda>1/2\), the active intervals in (2) start at
\(4(1+\lambda)j+O(1)>d_j/2\). In each of the three active residue classes,
the lower part of \(U_j\) is therefore also uncontrolled. Adding those three
pieces to the class-5 piece gives

\[
 \log D_{j,L}\ge3\lambda j+o(j).                \tag{19}
\]

Both estimates follow directly from (4). They leave a uniform positive
decimal margin:

\[
 \begin{cases}
 \frac32j-L\log10\ge(\frac32-\frac12\log10)j+o(j)>0,
    &L\le j/2,\\[1mm]
 3L-L\log10=(3-\log10)L+o(j)>0,
    &L>j/2.
 \end{cases}                                      \tag{20}
\]

All prime factors of \(Q_j\) come from 5, 239, or an odd linear denominator
at most \(12j+5\), so

\[
 \omega(D_{j,L})\le\pi(12j+5)=o(j).              \tag{21}
\]

Kanold's theorem, as sourced in the companion report, gives
\(J(D)\le2^{\omega(D)}\). Vary the numerator at the same denominator by

\[
 a'=a_j+F_{j,L}m\pmod {Q_j},\qquad m\pmod {D_{j,L}}. \tag{22}
\]

These fractions retain every controlled component. Because the step is a
unit modulo \(D_{j,L}\), consecutive choices in (22) that remain coprime to
\(Q_j\) have cyclic gap at most

\[
 \frac{J(D_{j,L})}{D_{j,L}}
 \le\frac{2^{\omega(D_{j,L})}}{D_{j,L}}.         \tag{23}
\]

Equations (18)--(21) imply, uniformly for \(1\le L\le2j+O(1)\) once \(j\)
is sufficiently large,

\[
 \frac{2^{\omega(D_{j,L})}}{D_{j,L}}<10^{-L}.   \tag{24}
\]

Hence (22) contains a reduced numerator \(a'\), at the same actual \(Q_j\)
and with all the same components in (17), in the length-\(L\) cylinder
whose word is \(55\ldots5\). Put \(x=a'/Q_j\). Then

\[
 \{10^t x\}\in[0.5,0.6)\qquad(0\le t<L).       \tag{25}
\]

The exact actual forcing can also be retained. Define

\[
 z_t:=\left\{10^tx+R_{j,t}\right\},\qquad
 R_{j,t}:=\sum_{u=0}^{t-1}10^{t-1-u}\Delta_{j+u}.
\]

Then

\[
 z_{t+1}=\{10z_t+\Delta_{j+t}\},\qquad
 R_{j,t}=10^ts_j^{\rm err}-s_{j+t}^{\rm err},\qquad
 0\le R_{j,t}<10^t\rho^j,                        \tag{26}
\]

where \(s_n^{\rm err}=10^n(\pi-M_{3n})\) and
\(\rho=10/5^{12}\). Every forcing increment inside a common active pulse is
\(p\)-integral, so (26) preserves all components in \(S_{j,L}\). For
\(j\ge1\) and \(t\le2j\),

\[
 R_{j,t}<(100\rho)^j<4.1\cdot10^{-6}.            \tag{27}
\]

Thus the forced alternative orbit remains in \([0.5,0.601)\) and avoids
\([0,0.1)\) throughout the block. At its origin it retains the actual seed
denominator and the complete 5-/239-primary data; across the block it retains
every simultaneous T45 component and its propagation, while using the exact
forcing increments. No claim is made that its later reduced denominators
equal those of the actual Machin orbit.

The numerator \(a'\) is deliberately not the actual \(a_j\). Therefore this
does not refute a theorem about the selected Machin numerator. It strengthens
the companion separator by showing that **all overlapping T45-interior prime
pulses** can be frozen simultaneously and still do not force a hit. The actual residue
modulo \(D_{j,L}\) is the indispensable information.

## 5. Exact finite audits (`experiment`)

The deterministic script
[`multiprime_pulse_stats.py`](multiprime_pulse_stats.py) constructs the sets
in (2), forms their exact integer product, reconstructs (12), verifies every
local CRT component, and advances the projected rational by exact modular
arithmetic. Decimal-cell counts are exact. The reported logarithms and
Fourier magnitudes use ordinary floating-point arithmetic and are diagnostic
only.

For blocks of length \(j/2\), it returned:

| \(j\) | \(L\) | active primes | \(\log P/j\) | \(\log\prod_{\ell\in U_j\setminus S}\ell/j\) | distinct 1/2/3-digit cells | \(\max_{1\le h\le20}|T^{-1}\sum e_P(hA_j10^t)|\) |
|---:|---:|---:|---:|---:|---:|---:|
| 100 | 50 | 66 | 4.4684 | 1.5578 | 9 / 38 / 50 | 0.2370 |
| 500 | 250 | 267 | 4.4762 | 1.4617 | 10 / 92 / 223 | 0.1054 |
| 1,000 | 500 | 492 | 4.4670 | 1.4802 | 10 / 100 / 375 | 0.0980 |
| 5,000 | 2,500 | 2,114 | 4.5206 | 1.4926 | 10 / 100 / 924 | 0.0386 |

At \(j=5000\), the single-time active set has 2,848 primes and
\(\log P/j=6.00585\); all primes born by that time number 4,537 and have
product logarithm divided by \(j\) equal to 8.96782. These finite values
check the constants 6, 4.5, and 9 in the asymptotic calculation. The apparent
projection cancellation is finite evidence only and supplies no bound for
later \(j\). The upper-half-complement column checks the coefficient 1.5 at
\(L=j/2\). At \(j=1000\) and lengths 750, 1000, 1500, and 1800, its measured
logarithmic coefficients were 2.2529, 2.9576, 4.4960, and 5.3950, respectively,
consistent with the separate `proof sketch` prediction \(3L/j\).

The exact rational checker
[`multiprime_same_modulus_check.py`](multiprime_same_modulus_check.py)
then tested the stronger Section 4 construction at the **actual** denominator.
For every \(2\le j\le100\) and
\(L\in\{1,\lfloor j/2\rfloor,j,2j\}\), it verified upper-half survival,
exponent one for every active prime, \((F_{j,L},D_{j,L})=1\), and the finite
sufficient inequality

\[
 D_{j,L}>2^{\omega(D_{j,L})}10^L.
\]

All 394 distinct block checks passed. At \(j=100\), the cofactor data
\((L,\operatorname{bits}D,\omega(D))\) were
\((1,858,106)\), \((50,1055,128)\), \((100,1271,151)\), and
\((200,1689,193)\). This is an `experiment`; the proof-sketch asymptotic
argument is separate.

The separate exact GMP program
[`multiprime_orbit_den_gmp.cpp`](multiprime_orbit_den_gmp.cpp) records the
reduced denominator of the actual rational \(\{y_j\}\). Its retained output
is [`multiprime_orbit_den_1000.tsv`](multiprime_orbit_den_1000.tsv).

| \(j\) | denominator bits | `(bits * log 2) / j` | \(v_5(Q_j)\) | \(v_{239}(Q_j)\) |
|---:|---:|---:|---:|---:|
| 100 | 13,781 | 95.5226 | 1,103 | 1,205 |
| 500 | 68,825 | 95.4117 | 5,503 | 6,005 |
| 1,000 | 137,643 | 95.4069 | 11,003 | 12,005 |

The bit-derived log ratio has error less than \((\log2)/j\). Through this
finite range it is close to the natural scale 95.4214, while the half-block
active product occupies about 4.7% of that logarithm. This is an
`experiment`, not a proof that reduction remains small asymptotically.

Reproduction commands were:

```bash
python -m py_compile work/ultrapi-resume/multiprime_pulse_stats.py
python work/ultrapi-resume/multiprime_pulse_stats.py \
  --pair 100:50 --pair 500:250 --pair 1000:500 --pair 5000:2500

python -m py_compile work/ultrapi-resume/multiprime_same_modulus_check.py
python work/ultrapi-resume/multiprime_same_modulus_check.py \
  --min-j 2 --max-j 100

podman run --rm -v "$PWD:/workspace:Z" -w /workspace \
  localhost/allmath-research:latest bash -lc \
  'g++ -O3 -DNDEBUG -std=c++23 \
     work/ultrapi-resume/multiprime_orbit_den_gmp.cpp \
     -lgmpxx -lgmp -o /tmp/multiprime_orbit_den_gmp && \
   /tmp/multiprime_orbit_den_gmp 1000 \
     /workspace/work/ultrapi-resume/multiprime_orbit_den_1000.tsv'
```

Artifact hashes at the end of the run were:

```text
multiprime_pulse_stats.py       92d56aa6082afec13d46cb2246adde4b9ec3dcf62c8e73c63fabdb8e9512dae4
multiprime_same_modulus_check.py dfab08de96dde371a11a4cb5027f5b07243250a2cf2eb6c7849239d5f0e2d635
multiprime_orbit_den_gmp.cpp    ba4d09c2abd3cd91b65b5de60d0f94a4ad569ae28649308f337ede158989c0b7
multiprime_orbit_den_1000.tsv    708e7ab78fdf08523ac3a6a1579f9d1859eabcee851b30839fd176f1a0726668
```

## 6. Literature boundary (`literature-checked`)

The dated source audit in
[`literature_report.md`](literature_report.md) was rechecked against the new
multi-prime formulation, and targeted searches for squarefree-composite
geometric sums, CRT-idempotent sums, and lacunary rational orbits found no
applicable theorem.

- [Kerr, *Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170)
  treats one prime modulus. It can address an individual projection but not
  the complementary correlated phase.
- [Bourgain--Chang, *Exponential sum estimates over subgroups and almost
  subgroups of \(\mathbb Z_q^*\)*](https://math.ucr.edu/~mcc/paper/122%20NewExp.pdf)
  requires polynomial-size orbit/order hypotheses such as \(T>q^\delta\).
  Here \(q=P=\exp(\Theta(j))\) and \(T=\Theta(j)=\Theta(\log P)\).
- [Bailey--Crandall, *Random Generators and Normal Numbers*](https://www.davidhbailey.com/dhbpapers/bcnormal.pdf)
  records a coprime composite-modulus discrepancy route whose useful scale is
  roughly square-root in the modulus, again far above logarithmic length.
- Ramaré--Rumely's explicit fixed-modulus estimates support the weighted
  prime-product calculation (5), but say nothing about the decimal digits of
  the CRT numerator (12).

The exact character collapse (9)--(15) means that a theorem about independent
prime coordinates would in any case be aimed at the wrong object. The missing
estimate is for one selected rational seed, not for an average over CRT
components.

## 7. Remaining actual-numerator problem

Write the actual reduced pulse origin as

\[
 y_j=\frac{a_j}{Q_j},\qquad
 P_{j,L}:=\prod_{p\in S_{j,L}}p,\qquad
 Q_j=P_{j,L}\widetilde D_{j,L}.
\]

CRT decomposes its phase into the forced prime coordinate and a complementary
coordinate. On the common block, both are multiplied by the same \(10^t\):

\[
 e(hy_{j+t})=
 e_{P_{j,L}}(hA_j10^t)\,
 e_{\widetilde D_{j,L}}(hE_j10^t)\,
 e(hR_{j,t}). \tag{28}
\]

The first factor is now explicit through (10)--(12), and the last factor is
negligible. The middle factor contains the overwhelming unresolved
cofactor information. Cancellation of the first factor alone gives no bound
for the product; the separator shows that a complementary factor can encode
an avoiding prefix while preserving every active prime law.

Therefore the next result with V1 leverage would have to control the **actual
pair** \((A_j,E_j)\), equivalently the complete selected numerator \(a_j\), in
an estimate such as

\[
 \left|\sum_{0\le t<T}e_{Q_j}(ha_j10^t)\right|=o(T)
 \quad(T\asymp j), \tag{29}
\]

uniformly over the finite frequencies needed for a prescribed decimal cell,
for suitable infinitely many blocks. No such estimate is proved or located.

## Bottom line

The simultaneous-prime idea reaches a clean stopping theorem at `proof
sketch` status. There really are linearly many logarithmic bits of exact,
route-specific denominator information: \(\log P\sim6j\) at one time. But
all those components collapse to one character-weighted CRT numerator, and
an all-components rational separator survives the exact Machin forcing.

This rules out the hoped-for generic bridge

\[
 \text{many overlapping T45 pulses}\Longrightarrow
 \text{archimedean decimal coverage}.
\]

It does not rule out a theorem exploiting the actual Machin numerator. It
identifies that numerator's complementary CRT phase as the precise remaining
obligation. No complete proof or candidate resolution of V1 is claimed.
