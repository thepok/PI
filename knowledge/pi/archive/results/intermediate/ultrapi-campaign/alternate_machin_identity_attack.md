# Alternate Machin identities: exact coupling, not independent mixing

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.  
Route: compare a genuinely different coprime-base Machin truncation with the
existing \(5/239\) truncation used in T36--T55.

## Outcome and exact claim status

No proof that every finite decimal word occurs in pi was obtained. The
canonical V1 target remains a `conjecture`.

There is a useful exact conclusion. Let \(M_K\) be the existing rational
\(5/239\) lower approximant, and let \(H_K\) be the even Taylor truncation of

\[
 {\pi\over4}=2\arctan {1\over3}+\arctan {1\over7}.            \tag{1}
\]

At the two natural schedules used below,

\[
                         M_{3j}<H_{5j}<\pi\qquad(j\ge1).       \tag{2}
\]

Both errors are smaller than \(10^{-8j}\). Thus the second identity really
does provide a different, sharper rational shadow of the same decimal orbit.
It also provides large denominator coordinates involving the bases \(3\) and
\(7\), rather than \(5\) and \(239\).

The hoped-for independence nevertheless fails exactly. With

\[
 d_j=10^j(H_{5j}-M_{3j}),
\]

the two sampled circle states and their forcing increments obey

\[
 \{10^jH_{5j}\}=\{\{10^jM_{3j}\}+d_j\},                     \tag{3}
\]

\[
 \Delta^H_j-\Delta^M_j=d_{j+1}-10d_j.                        \tag{4}
\]

Thus the two recurrences are related by an explicit rational translation and
an exact coboundary. After lifting both reduced fractions to their least
common denominator, their residues lie on one affine graph of cardinality
\(L\), not in an independent product of cardinality \(L^2\). The new
prime-power coordinates are carried by the offset \(d_j\); they do not give a
second equation for the unknown Archimedean tail.

Equations (2)--(4), the common-denominator graph, and the separator below have
status `proof sketch`: all algebraic arguments are displayed but have not
been formalized in Lean. The exact finite replay is an `experiment`. The
identity and Taylor-series source audit is `literature-checked` as of the
date above. Nothing here is a V1 resolution.

## 1. Normalized statement and quantifier boundary

The target is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^m\;
 \exists s\in\mathbb N:\quad
 (d_s(\pi),\ldots,d_{s+m-1}(\pi))=w.                         \tag{V1}
\]

Leading zeroes are allowed, \(m=0\) is vacuous, and occurrence is contiguous.
This branch studies whether two exact formulas for the same fixed number can
create independent modular information. It does not replace the existential
start \(s\) by a prescribed start, and it does not assume normality.

## 2. Source and mathlib audit

The literature and library search was rerun before constructing the second
family.

- DLMF [4.24.E3](https://dlmf.nist.gov/4.24.E3) gives the arctangent Taylor
  series used below.
- Farhi, [arXiv:2601.10300v1, equations (1.5) and
  (2.9)](https://arxiv.org/abs/2601.10300), records Euler's identity
  \(\arctan(1/2)+\arctan(1/3)=\pi/4\) and studies refinements as rational
  approximations. No prescribed-digit distribution theorem is stated there.
- The pinned local mathlib checkout at commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f` contains all four classical
  unit-fraction identities in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`, including
  `arctan_inv_2_add_arctan_inv_3`,
  `two_mul_arctan_inv_3_add_arctan_inv_7`, and
  `four_mul_arctan_inv_5_sub_arctan_inv_239`. The source-file SHA-256 is
  `f2503a1e4710591b3dbadf5502e2dd14681b4f69c0498d1cb073ecd634c65238`.

There is an important identity screen. Put

\[
 a=\arctan(1/2),\qquad b=\arctan(1/3),\qquad c=\arctan(1/7).
\]

The addition formula gives \(a=b+c\), since

\[
 {1/3+1/7\over1-1/21}={1\over2}
\]

and all three angles are in the required principal range. Consequently

\[
 a+b=2b+c=2a-c=\pi/4.                                      \tag{5}
\]

Euler's, Hutton's, and Hermann's formulas are therefore just the three faces
of this one triangular relation. Treating two of them as independent would
be a false start. We instead compare Hutton's \(3/7\) formula (1) against
Machin's genuinely different \(5/239\) formula.

The branch choices can be checked without floating point by Gaussian integer
certificates:

\[
 (3+i)^2(7+i)=50(1+i),                                      \tag{6}
\]

\[
 (5+i)^4(239-i)=114244(1+i).                                \tag{7}
\]

Dividing each equality by its conjugate gives the corresponding unit-circle
identity. Positivity of the displayed angles selects \(\pi/4\), rather than a
different value modulo \(\pi\). Equations (6) and (7) also show that the two
chosen representations have genuinely different Gaussian factorizations.

## 3. Exact rational truncations and tails

For \(q\ge2\), define

\[
 T_q(N)=\sum_{n=0}^{N-1}{(-1)^n\over(2n+1)q^{2n+1}}.         \tag{8}
\]

The existing T36 approximant is

\[
 M_K=16T_5(2K+2)-4T_{239}(2K+3).                            \tag{9}
\]

Define the alternate coprime-base lower approximant

\[
 H_K=8T_3(2K+2)+4T_7(2K+2).                                \tag{10}
\]

Every even partial sum lies below its arctangent. Since the coefficients in
(1) are positive, \(H_K<\pi\), and the strict alternating-tail estimate gives

\[
 0<\pi-H_K
 <{8\over(4K+5)3^{4K+5}}+{4\over(4K+5)7^{4K+5}}
 <81^{-K}.                                                   \tag{11}
\]

T36 machine-checks \(0\le\pi-M_K<625^{-K}\). In particular,

\[
 \pi-H_{5j}<81^{-5j}<10^{-8j},\qquad
 \pi-M_{3j}<625^{-3j}<10^{-8j},                             \tag{12}
\]

because \(81^5=3486784401>10^8\) and
\(625^3=244140625>10^8\).

The two lower approximants can actually be ordered for every \(j\ge1\), not
just numerically. For \(r=12j+5\), the first two omitted \(1/5\) terms give

\[
 \pi-M_{3j}>
 {384\over25r5^r}.                                          \tag{13}
\]

For \(R=20j+5\), (11) gives

\[
 \pi-H_{5j}<{12\over R3^R}.                                \tag{14}
\]

The desired comparison between (13) and (14) is exactly

\[
 32(20j+5)3^{20j+5}>25(12j+5)5^{12j+5}.                    \tag{15}
\]

At \(j=1\), its two sides are respectively
\(677830887554400\) and \(324249267578125\). The ratio of the left/right
quotient at \(j+1\) to the quotient at \(j\) is

\[
 {20j+25\over20j+5}{12j+5\over12j+17}{3^{20}\over5^{12}}>1. \tag{16}
\]

The product of the first two factors is already greater than one (the
cross-products differ by \(40\)), and \(3^{20}>5^{12}\). This proves (15)
for all \(j\ge1\), hence (2).

So the alternate representation is not merely another loose bracket: on
this schedule it is always the tighter lower approximant.

### Strongest computable-interval consequence

The ordering can be sharpened to the complete adjacent alternating brackets.
Define

\[
 U^H_K=8T_3(2K+3)+4T_7(2K+3),                              \tag{17}
\]

\[
 U^M_K=16T_5(2K+3)-4T_{239}(2K+2).                         \tag{18}
\]

The changed parities make both expressions rational upper bounds for pi.
In fact, for every \(j\ge1\),

\[
 M_{3j}<H_{5j}<\pi<U^H_{5j}<U^M_{3j}.                     \tag{19}
\]

The first half is (2). For the upper half, the same two-term alternating
estimate reduces the comparison, for \(j\ge2\), to

\[
 32(20j+7)3^{20j+7}>25(12j+7)5^{12j+7}.                   \tag{20}
\]

Its quotient grows by a factor greater than \(3^{20}/5^{12}>1\), and it is
already true at \(j=2\). The remaining \(j=1\) case is the exact positive
rational identity

\[
 U^M_3-U^H_5=
 {3229464300889108415204694412175922488180171512184029195146198880914267164
 \over
 436724294671580962626257793948074605191880297970023941297822369042342801935577392578125}.
                                                                    \tag{21}
\]

Consequently, with

\[
 I^H_j=[H_{5j},U^H_{5j}],\qquad I^M_j=[M_{3j},U^M_{3j}],
\]

one has the exact quantified statement

\[
 \forall j\ge1:\qquad
 \pi\in I^H_j\subsetneq I^M_j,\qquad I^H_j\cap I^M_j=I^H_j.          \tag{22}
\]

The two-identity intersection is therefore **exactly the Hutton bracket**;
it is not smaller than the bracket supplied by the better identity alone.
Its fully computable rational width is

\[
 |I^H_j|=
 {8\over(20j+5)3^{20j+5}}+
 {4\over(20j+5)7^{20j+5}}.                                 \tag{23}
\]

This interval is genuinely usable for a finite word certificate, with the
following exact quantifiers. For every \(j\ge1\), \(m\ge0\),
\(0\le a<10^m\), and \(z\in\mathbb Z\), if

\[
 z+{a\over10^m}\le10^jH_{5j}
 \quad\hbox{and}\quad
 10^jU^H_{5j}<z+{a+1\over10^m},                             \tag{24}
\]

then

\[
 \left\lfloor10^m\{10^j\pi\}\right\rfloor=a.                \tag{25}
\]

Thus (24) proves that the length-\(m\) word encoded by \(a\), including
leading zeroes, occurs at the prescribed start \(j\). A sufficient assertion
that would close V1 through these brackets is

\[
 \forall m\;\forall a<10^m\;\exists j\ge1\;\exists z\in\mathbb Z:
 \text{condition (24)}.                                    \tag{26}
\]

Condition (26) is stronger than V1: an actual occurrence need not be
certified by this particular scheduled bracket, and (26) excludes start
zero. Neither bracket nesting nor the affine coupling proves it. The interval
does certify any individual finite hit for which (24) is checked, but a
finite list of such checks remains an experiment.

## 4. Exact translation and forcing coboundary

Write

\[
 m_j=M_{3j},\qquad h_j=H_{5j},
\]

\[
 v_j=\{10^jm_j\},\qquad u_j=\{10^jh_j\},\qquad
 d_j=10^j(h_j-m_j).                                         \tag{27}
\]

Then \(d_j>0\), and the elementary identity
\(\{\{x\}+y\}=\{x+y\}\) proves (3) exactly. Define the rational forcing
increments

\[
 \Delta^M_j=10^{j+1}(m_{j+1}-m_j),\qquad
 \Delta^H_j=10^{j+1}(h_{j+1}-h_j).                          \tag{28}
\]

Both streams obey their usual forced decimal recurrences,

\[
 v_{j+1}=\{10v_j+\Delta^M_j\},\qquad
 u_{j+1}=\{10u_j+\Delta^H_j\}.                              \tag{29}
\]

Direct subtraction gives the exact coboundary (4):

\[
 \begin{aligned}
 d_{j+1}-10d_j
 &=10^{j+1}\bigl((h_{j+1}-h_j)-(m_{j+1}-m_j)\bigr)\\
 &=\Delta^H_j-\Delta^M_j.
 \end{aligned}                                               \tag{30}
\]

The relation to the actual Archimedean tail is even more explicit. Put

\[
 s^M_j=10^j(\pi-m_j),\qquad s^H_j=10^j(\pi-h_j).
\]

Then

\[
                       d_j=s^M_j-s^H_j,                      \tag{31}
\]

and

\[
 \{10^j\pi\}=\{v_j+s^M_j\}=\{u_j+s^H_j\}.                 \tag{32}
\]

Thus the two nominal tail variables have rank one: specifying either one
specifies the other. The second representation improves the error size, but
it does not create a second independent Archimedean observation.

Under the same explicit source-level premise \(\mu(\pi)<8\) used in T36,
the bound (12) lets the standard boundary-transfer argument show that, for
each fixed block length, the two rational code streams and the pi code stream
are eventually equal. This remains a conditional representation theorem. It
does not prove that the common stream visits every code.

## 5. The common-denominator affine graph

Put the two scheduled rationals in lowest terms:

\[
 m_j={A_j\over Q_j},\qquad h_j={B_j\over R_j},
\]

and let \(L_j=\operatorname{lcm}(Q_j,R_j)\). Lift the numerators to

\[
 \bar A_j=A_j{L_j\over Q_j},\qquad
 \bar B_j=B_j{L_j\over R_j}.                                \tag{33}
\]

Then

\[
 h_j-m_j={\bar B_j-\bar A_j\over L_j}.                       \tag{34}
\]

For the sampled lifted residues

\[
 \rho^M_j\equiv10^j\bar A_j\pmod {L_j},\qquad
 \rho^H_j\equiv10^j\bar B_j\pmod {L_j},
\]

one has

\[
 \boxed{\rho^H_j-\rho^M_j
 \equiv10^j(\bar B_j-\bar A_j)\pmod {L_j}.}                 \tag{35}
\]

If one lets the first residue range over \(\mathbb Z/L_j\mathbb Z\), the
admissible pairs in (35) form one affine graph with exactly \(L_j\) points.
Treating the two lifted residues as independent would incorrectly replace
that graph by \(L_j^2\) pairs. The actual two formulas select one point of the
graph.

This also locates what happens to apparently new prime-power information.
For any prime \(p\), the non-Archimedean equality

\[
 v_p(x)\ne v_p(y)\quad\Longrightarrow\quad
 v_p(x-y)=\min\{v_p(x),v_p(y)\}                              \tag{36}
\]

shows that a stronger denominator coordinate present in \(h_j\) but absent
from \(m_j\) survives exactly in \(h_j-m_j\). It is absorbed by the known
translation in (34), rather than becoming an independent constraint on the
Machin coarse state. Conversely, discarding the offset discards precisely
the new coordinate one hoped to exploit.

Safe natural denominators make the different arithmetic visible. If

\[
 \Lambda_K=\operatorname{lcm}\{1,3,\ldots,4K+3\},
\]

then the reduced denominator of \(H_K\) divides

\[
                 \Lambda_K3^{4K+3}7^{4K+3}.                 \tag{37}
\]

The analogous natural denominator for \(M_K\) divides

\[
 \operatorname{lcm}\{1,3,\ldots,4K+5\}
       5^{4K+3}239^{4K+5}.                                  \tag{38}
\]

These are genuinely different factorizations. Equation (35), not a
probabilistic independence heuristic, is the exact way they combine.

This is a separator for the proposed shortcut, not for every possible use of
the alternate identity. A new theorem controlling the ordered residues of
the offset (34), or jointly controlling a residue and that offset, could
still be useful. No such theorem was found in the source search or proved
here.

## 6. Structural two-denominator separator

The failure is not peculiar to these coefficients. Consider the explicit
irrational

\[
 \beta=\sum_{n=2}^{\infty}10^{-n!}.                          \tag{39}
\]

Its decimal expansion uses only \(0\) and \(1\), has unbounded gaps between
ones, and is not eventually periodic. Hence it is irrational and omits the
one-digit word \(2\).

For each sample index \(j\), choose powers \(B_j=2^{a_j}\) and
\(C_j=3^{b_j}\) as large as needed. Let \(P_j\) be the largest odd integer
below \(B_j\beta\), and let \(S_j\) be the largest integer below
\(C_j\beta\) that is not divisible by \(3\). Then

\[
 0<\beta-{P_j\over B_j}<{2\over B_j},\qquad
 0<\beta-{S_j\over C_j}<{3\over C_j},                       \tag{40}
\]

and both displayed denominators are reduced and coprime. Since the powers
can be chosen arbitrarily large, the errors can be made smaller than the
positive distance from each finite scaled beta orbit point to the relevant
decimal boundaries. Both rational streams can therefore shadow every desired
finite portion of beta's digit orbit.

They obey the same exact translation, affine-graph, and forcing-coboundary
identities (3)--(4) and (35), now with completely different coprime
prime-power denominators. Yet their common limiting digit stream omits \(2\).
This proves that "two fast rational shadows with independent-looking
denominators" plus the universal coupling identities cannot imply V1.

The separator deliberately does not reproduce the special local numerator
formulas of the two Machin series. It leaves open the only honest remaining
possibility: a theorem using a specific, non-universal correlation of the
actual \(3/7\), \(5/239\), and decimal residues.

## 7. Exact replay

The companion checker is
[`alternate_machin_identity_check.py`](alternate_machin_identity_check.py),
SHA-256
`c33fd951ecf8e8bab72972538a9d2185c115d41fcc4a95ae8173588c3f805b5f`.
It uses Python `Fraction` arithmetic throughout. A clean run reports:

```text
claim_status=experiment
gaussian_integer_exact_checks=5
partial_sum_recurrence_exact_checks=62
natural_denominator_divisibility_exact_checks=62
tail_order_integer_exact_checks=399
nested_rational_exact_checks=40
nested_alternating_bracket_exact_checks=80
sampled_coboundary_and_circle_exact_checks=80
common_denominator_affine_graph_exact_checks=80
all exact assertions passed
```

For \(1\le j\le10\), the actual reduced \(H_{5j}\) denominators have
three- and seven-adic exponents growing roughly linearly, while the common
denominator has 293 to 2440 bits. In 7 of those 10 rows the reduced offset
denominator has exactly the full common-denominator bit length; in the other
three it loses only 5, 14, and 11 bits. This finite table is an `experiment`,
not an asymptotic theorem, but it is consistent with the exact absorption
mechanism (36) and strongly falsifies the idea that subtraction usually
makes the new coordinates disappear.

## 8. Sharp conclusion

The alternate identity produces real mathematical progress: a new explicit
coprime-base lower family, the all-\(j\) ordering (2), and a much sharper
rational shadow with very different denominator arithmetic. But two
representations of the same constant do not act like independent random
samples. Their tails differ by the exact rational offset, their recurrences
differ by a coboundary, and their lifted residues occupy one affine graph.

Accordingly, the route does **not** determine or mix the remaining
Archimedean coarse/fine state. It relocates that state into the cross-identity
offset. A viable continuation would need a quantitative theorem about the
ordered residues of that specific offset (or a genuinely joint exponential
sum), not a second CRT decomposition alone.
