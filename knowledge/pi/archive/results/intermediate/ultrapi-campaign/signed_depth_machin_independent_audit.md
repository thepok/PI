# Independent audit: signed, depth-varying Machin shadows

Audit date: **2026-08-12 UTC**  
Audited report:
[`signed_depth_machin_attack.md`](signed_depth_machin_attack.md)  
Audited report SHA-256:
`87dfb60e128a7ea5a321af93c5b99065461133966f14bb68c1248fcd64d50ce9`  
Primary checker:
[`signed_depth_machin_attack_check.py`](signed_depth_machin_attack_check.py)  
Primary checker SHA-256:
`f2ef77adf962217bce6d3f8884d461fa0d0502f9d0f67e302a587016a2aa8206`  
Independent checker:
[`signed_depth_machin_independent_check.py`](signed_depth_machin_independent_check.py)  
Independent checker SHA-256:
`83eeedc5d531a9727359cb14adc5db6796684713dcaf8a95d69df7814972977b`

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Canonical target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Original source URL: none; the immutable local source records none, and no URL
was invented.

## Verdict and claim status

**PASS.** The two signed Machin identities, the alternating-remainder bounds,
the seven displayed reduced-denominator/error rows, both deep-cancellation
inequalities, both infinite score-separated valuation families, the 2059
11-adic cancellation, and the modular lifts all independently rederive. The
fixed-prime synchronization squeeze is also logically sound with its stated
fixed-data and height hypotheses.

The analytic and valuation deductions have status `proof sketch`; the finite
replays have status `experiment`; and the bounded primary-source audit is
`literature-checked` as of 2026-08-12 UTC. There is no Lean formalization in
this branch.

**No result in the report proves V1.** Canonical V1 remains a `conjecture`.
This work is not a `candidate resolution`: it excludes only shadows with a
fixed prime surviving linearly at exponential rational height, and proves that
premise only on two selected infinite depth families.

## 1. Fixed-prime squeeze with all quantifiers exposed

The report's obstruction can be stated without the informal word “height” as
follows. Fix:

- an integer (c\ge2) multiplicatively independent of (10);
- a prime (p\nmid10c); and
- constants (\kappa,C>0).

For each (j), let (H_j>0), (N_j\in\mathbb N), and let
(A_j=P_j/q_j) be reduced with (q_j\ge1). Assume (H_j\to\infty) and,
for all sufficiently large (j),

\[
 q_j\mid10^{N_j}-c,\qquad
 v_p(q_j)\ge\kappa H_j,\qquad
 \log q_j\le C H_j.                                    \tag{A1}
\]

Then the proof actually gives the stronger conclusion

\[
 \frac{|\pi-A_j|}{10^{-N_j}}\longrightarrow\infty.     \tag{A2}
\]

In particular, (|\pi-A_j|\ne o(10^{-N_j})). No separate hypothesis
(N_j\to\infty) is needed: it follows from (A1) and Yu's estimate.

To check the cited (p)-adic step, apply Yu's Theorem 1 to

\[
 \Xi=10^{N}c^{-1}-1
\]

with fixed algebraic numbers (10,c) and exponents (N,-1). Since
(p\nmid10c), both algebraic numbers are (p)-adic units. For the technical
field condition in Yu's statement one may use (K=\mathbb Q) when
(p\equiv3\pmod4), and (K=\mathbb Q(i)) when
(p\equiv1\pmod4). The rational valuation is unchanged at a prime above
(p). Multiplicative independence makes (Xi\ne0), all algebraic heights
are fixed, and Yu's parameter (B) is (O(N)). Hence, for a constant
(C_{p,c}>0),

\[
 v_p(10^N-c)=v_p(10^Nc^{-1}-1)
 \le C_{p,c}\log N.                                    \tag{A3}
\]

Combining (A1) and (A3) gives

\[
 N_j\ge \exp(\kappa' H_j)                              \tag{A4}
\]

for fixed (kappa'>0). Also (q_j\to\infty), because
(q_j\ge p^{\kappa H_j}). Zeilberger--Zudilin's bound
(mu(\pi)\le7.103205334137\ldots<8), together with the definition of
irrationality measure, therefore gives, for all sufficiently large (j),

\[
 |\pi-P_j/q_j|>q_j^{-8}\ge e^{-8CH_j}.                  \tag{A5}
\]

Consequently

\[
 \frac{|\pi-A_j|}{10^{-N_j}}
 \ge \exp\!\left((\log10)e^{\kappa'H_j}-8CH_j\right)
 \longrightarrow\infty,                               \tag{A6}
\]

which proves (A2). The numerator (P_j) needs no separate height bound.
The label (H_j) is merely an auxiliary scale; only the two inequalities in
(A1) matter.

The report's sentence about (p\mid c) is read with the ambient condition
(p\nmid10): then (10^N-c\not\equiv0\pmod p), so divisibility by (p)
is impossible. Thus the cases used later are exhaustive: absence of the
first congruence is a direct obstruction, (p\mid c) is a direct
obstruction, and (p\nmid10c) is covered by the squeeze.

## 2. Exact identities and branch selection

Independent integer multiplication gives

\[
 (3+i)^3(11-2i)=250+250i,
\]

\[
 (7+i)^6(22049-1457i)
 =1953125000+1953125000i.                               \tag{A7}
\]

Also (22049=17\cdot1297), both factors are prime, and
(\gcd(1457,22049)=1). These products establish the identities modulo
(pi). Their actual arguments lie strictly between (0) and (1<\pi/2):
the negative angle is smaller than the positive angle in each identity, and
the report's elementary upper bounds control the total. Hence the relevant
branch is exactly (pi/4), not merely a congruence modulo (pi).

For (R\equiv1\pmod4), integrating the finite geometric identity

\[
 \frac1{1+t^2}
 =\sum_{k=0}^{(R-3)/2}(-1)^k t^{2k}
   +\frac{t^{R-1}}{1+t^2}
\]

gives exactly

\[
 \rho_R(x)=\int_0^x\frac{t^{R-1}}{1+t^2}\,dt,
 \qquad
 \frac{x^R}{R(1+x^2)}\le\rho_R(x)\le\frac{x^R}{R}.     \tag{A8}
\]

For the (3,11) identity, (A8) yields

\[
 4\{3\rho_R(1/3)-\rho_R(2/11)\}
 \ge \frac{4\,3^{-R}}R
       \left(\frac{27}{10}-\left(\frac6{11}\right)^R\right)
 \ge \frac{474}{55}\frac{3^{-R}}R>0.                  \tag{A9}
\]

The general largest-argument inequality follows from the reverse triangle
inequality and the two sides of (A8). Its “eventually” qualifier is essential
and is present in the report.

## 3. Independent finite replay

The independent checker uses twelve alternating terms rather than the
primary checker's ten. It confirms both relative-cancellation statements:

\[
 \frac{|E_{6209,4001}|}
 {4\{3\rho_{6209}(1/3)+\rho_{4001}(2/11)\}}<\frac1{4000},
\]

\[
 \frac{|\pi-B_{125,89}|}
 {4\{6\rho_{125}(1/7)+\rho_{89}(1457/22049)\}}<\frac1{1400}. \tag{A10}
\]

It independently constructs and reduces every rational shadow in the
report's seven-row table. All seven denominator digit counts and all seven
values of
(lfloor\log_{10}(q\,|E|_{\rm certified})\rfloor) agree, and every exact
lower bound has (q|E|>1). These are finite `experiment` results; they do not
justify an asymptotic claim.

The 2059 cancellation was also checked by a different computation. Scale
(L_{2061}(2/11)) by (11^{2059}) and reduce modulo (11^2=121). Every
term except exponents 2057 and 2059 vanishes modulo 121, while those two sum
to

\[
 22\pmod{121}.                                          \tag{A11}
\]

Thus the scaled prefix has exact 11-adic order one and

\[
 v_{11}(L_{2061}(2/11))=-2058.                          \tag{A12}
\]

This independently confirms both the cancellation and the report's warning
that a blanket endpoint-survival theorem is false.

The displayed residue chains solving (10^N\equiv16\pmod{17^k}) and
(10^N\equiv16\pmod{1297^k}) were checked against independently computed
multiplicative orders at every displayed level. They are the least
nonnegative compatible residues. As the report says, their observed growth
is not used as proof.

## 4. Infinite valuation families

For the (3,11) identity, take odd (e), (T=11^e), and (S=T+2).
Among the second-component exponents (r\le T), the denominator score is
(r+v_{11}(r)). The endpoint has score (T+e). Every earlier odd exponent
satisfies

\[
 r+v_{11}(r)\le(T-2)+(e-1)=T+e-3.                      \tag{A13}
\]

For an admissible first-omitted (R\equiv1\pmod4) with
(S\le R\le2T), every first-component term has 11-adic denominator order
at most (e). The endpoint is therefore the unique least-valuation term in
the full rational sum, proving

\[
 v_{11}(\operatorname{den}A_{R,S})=T+e.                 \tag{A14}
\]

The congruence (10^N\not\equiv16\pmod{11}) already excludes this family
for the fixed return (c=16).

For the (7,22049) identity, take (p=1297), (e\ge3), and
(S=p^e+4). The term (r=p^e) has score (p^e+e), the endpoint
(r=p^e+2) has score (p^e+2), every earlier term has score at most
(p^e+e-3), and the (1/7) component contributes order at most (e) when
(S\le R\le2p^e). Hence, again for admissible
(R\equiv1\pmod4),

\[
 v_{1297}(\operatorname{den}B_{R,S})=p^e+e.             \tag{A15}
\]

In both families, taking (H=\max(R,S)) makes the surviving valuation
linear in (H). A safe common denominator consists of fixed powers of the
argument denominators times an odd-index least common multiple, so its
logarithm is (O(H)); reduction can only lower it. This supplies exactly the
two premises needed by the fixed-prime squeeze.

The ranges in the report implicitly quantify only over admissible
first-omitted depths (R\equiv1\pmod4), because that condition is part of
the definition of (L_R). Read that way, both family statements are exact.

## 5. Source and provenance audit

The following primary sources were reopened on 2026-08-12 UTC:

- [DLMF 4.24.E3](https://dlmf.nist.gov/4.24.E3) gives the arctangent power
  series used in (A8). The integral remainder itself follows directly by
  finite geometric division and integration.
- Kunrui Yu,
  [*p-adic logarithmic forms and group varieties II*](https://matwbn.icm.edu.pl/ksiazki/aa/aa89/aa8944.pdf),
  Theorem 1, bounds the prime-ideal order of
  (alpha_1^{b_1}\cdots\alpha_n^{b_n}-1\) by fixed height factors times
  (log B). Its hypotheses and its use in (A3) were checked above.
- Doron Zeilberger and Wadim Zudilin,
  [*The Irrationality Measure of Pi is at most 7.103205334137...*](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/pimeas.pdf),
  state the definition of irrationality measure and prove the quoted upper
  bound. Exponent (8) in (A5) is therefore legitimate.

Matveev's theorem is mentioned by the primary report only as a possible
future tool and is not used to establish any audited conclusion. The report
correctly declines to infer a uniform full-tail bound from it.

The canonical target hash, report hash, and primary-checker hash in the
independent checker all match the files actually replayed. The primary
checker itself also completed with `all exact assertions passed` before the
independent run.

## 6. Remaining gap and exact non-resolution

The fixed-prime squeeze is conditional on a fixed prime satisfying

\[
 v_p(q_{R,S})\ge\kappa\max(R,S)                         \tag{A16}
\]

along the chosen schedule. The report proves (A16) only for the two
score-separated families above. Equation (A12) demonstrates that tied layers
can cancel, and no argument here controls every Archimedean-balanced depth
schedule after all within-component and cross-component cancellation. A
varying Machin identity can additionally move its denominator primes, so
there need not be any fixed (p) to which Yu's estimate applies.

Accordingly, the work closes a substantial fixed-prime mechanism but neither
constructs a divisor (q\mid10^N-c) with sufficiently small approximation
error nor proves that such divisors cannot exist in all other constructions.
It does not establish a decimal-cylinder hit for pi and does not prove V1.

## 7. Replay record

Commands run from the repository root:

~~~text
.venv/bin/python work/ultrapi-resume/signed_depth_machin_attack_check.py
.venv/bin/python work/ultrapi-resume/signed_depth_machin_independent_check.py
sha256sum problems/local/pi-digits.txt \
  work/ultrapi-resume/signed_depth_machin_attack.md \
  work/ultrapi-resume/signed_depth_machin_attack_check.py \
  work/ultrapi-resume/signed_depth_machin_independent_check.py
~~~

The independent run ended with:

~~~text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
report_sha256=87dfb60e128a7ea5a321af93c5b99065461133966f14bb68c1248fcd64d50ce9
primary_checker_sha256=f2ef77adf962217bce6d3f8884d461fa0d0502f9d0f67e302a587016a2aa8206
gaussian_certificates=PASS
independent_equal_depth_instances=100
independent_finite_rows=7
deep_signed_tail_balances=PASS
v11_den_L2061_2_over_11=2058
score_family_checks=18
modular_lift_chains=PASS
V1_proved=false
all independent exact assertions passed
~~~
