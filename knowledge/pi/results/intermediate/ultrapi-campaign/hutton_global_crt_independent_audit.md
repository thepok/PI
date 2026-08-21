# Independent audit: Hutton global CRT attack

Audit date: **2026-08-12 UTC**

Audited artifacts:

- [`hutton_global_crt_attack.md`](hutton_global_crt_attack.md)
- [`hutton_global_crt_check.py`](hutton_global_crt_check.py)
- the T61 inputs cited by the report

## Verdict

**PASS after one claim-label correction.**  I found no mathematical defect in
the definitions, local-to-global congruence, rational decomposition,
five-adic transient, additive-CRT coordinate, Jacobi identity, scale
obstruction, or the exact (K=3) falsifier.  The supplied exact checker passes,
and a separate exact-rational replay also passes.

The original report did contain one real audit defect: it said that T61
supplied the full local residue

\[
 pH_K\equiv\epsilon_p68/21\pmod p.
\]

T61 machine-checks the singular-pair formula, the cancellation-factor residue
(17), regular-block integrality, the valuation (-1), and denominator
multiplicity one, but it has no named Lean theorem stating this full residue.
I corrected the report to classify that local residue, and all CRT statements
depending on it, as `proof sketch`.  I also inserted its elementary deduction
from the formalized ingredients.  No formal file was changed, and the checker
needed no change.

This audit supplies no proof that every finite decimal word occurs in pi.
Canonical V1 remains a `conjecture`; the CRT identities remain `proof sketch`,
and every finite computation below remains an `experiment`.

## Exact definitions and domain

For (K\ge0), the report uses

\[
 R=4K+3,\qquad H_K=P_K/Q_K,
 \qquad \gcd(P_K,Q_K)=1,quad Q_K>0.
\]

It then defines

\[
 \mathcal P_K=\{p:R/2<p\le R,\ p\text{ prime},\ p>7,\ p\ne17\},
 \quad G_K=\prod_{p\in\mathcal P_K}p,
\]

\[
 \epsilon_p=(-1)^{(p-1)/2},\qquad
 S_K=\sum_{p\in\mathcal P_K}\epsilon_pG_K/p,
 \qquad C_K=Q_K/G_K.
\]

T61 gives (v_p(Q_K)=1) for each selected prime.  Hence (G_K\mid Q_K),
(C_K) is an integer, and exact multiplicity one gives
(\gcd(C_K,G_K)=1).  The remaining state definitions are

\[
 b_K=v_5(Q_K),\qquad m_K=Q_K/5^{b_K}=G_KB_K,
 \qquad B_K=m_K/G_K,
\]

\[
 a_K\equiv2^{b_K}P_K\pmod {m_K}.
\]

This (a_K) is the genuine post-transient decimal state, since

\[
 \{10^{b_K}H_K\}
 =\{2^{b_K}P_K/m_K\}=a_K/m_K.
\]

The checker consistently chooses the least nonnegative representative of
(a_K); the report only needs its residue class.

## Local residue, global congruence, and decomposition

Let (p\in\mathcal P_K).  The upper-half condition makes exponent (p) the
unique odd exponent in the Hutton prefix divisible by (p).  Multiplication by
(p) therefore kills every regular term modulo (p).  The singular pair gives

\[
 pH_K\equiv
 {4\epsilon_p(2\cdot7^p+3^p)\over3^p7^p}
 \equiv {4\epsilon_p(2\cdot7+3)\over3\cdot7}
 ={68\epsilon_p\over21}\pmod p.
\]

The inverses here exist because (p>7).  The condition (p\ne17) is needed both
for the valuation theorem and to keep (68) a unit.

Since (p) occurs once in (Q_K), the local congruence is equivalently

\[
 P_K\equiv {68\epsilon_p\over21}{Q_K\over p}
 ={68C_K\over21}\epsilon_p{G_K\over p}\pmod p.
\]

All terms of (S_K) except its (p)-term vanish modulo (p), so
(S_K\equiv\epsilon_pG_K/p\pmod p).  Thus

\[
 21P_K\equiv68C_KS_K\pmod p
\]

for every distinct prime factor of the squarefree (G_K), proving

\[
 \boxed{21P_K\equiv68C_KS_K\pmod {G_K}}.
\]

Consequently

\[
 T_K=(21P_K-68C_KS_K)/G_K\in\mathbb Z,
\]

and direct common-denominator arithmetic gives

\[
 H_K={68\over21}{S_K\over G_K}+{T_K\over21C_K}.
\]

No factor (C_K) may be dropped: it is precisely the conversion from the
local coordinate (pH_K) to the reduced numerator (P_K).

## Exact five-adic transient

Writing the shadow by odd exponent gives

\[
 H_K=\sum_{\substack{1\le r\le R\\r\text{ odd}}}
 {4(-1)^{(r-1)/2}(2\cdot7^r+3^r)\over r3^r7^r}.
\]

For odd (r), the cancellation factor is (2) modulo (5) when
(r\equiv1\pmod4), and (3) modulo (5) when (r\equiv3\pmod4); it is always a
5-unit.  Put (e=\lfloor\log_5R\rfloor) and (L=5^e).  Because (L\le R<5L)
and only odd multiples occur, the terms of minimum 5-adic valuation (-e)
are exactly (r=L), plus (r=3L) when (3L\le R).  After multiplication by
(5^e), their residues modulo (5) are respectively (3) and (1).  Their sum is
therefore (3) or (4), never zero.  Higher-valuation terms cannot cancel this
layer, so

\[
 v_5(H_K)=-e,
 \qquad v_5(Q_K)=e=\lfloor\log_5(4K+3)\rfloor.
\]

This includes the small cases: (K=0,R=3,b=0),
(K=1,R=7,b=1), (K=2,R=11,b=1), and (K=3,R=15,b=1).  My independent
exact replay checked every (0\le K\le90), including transitions

```text
K=0,  R=3,   e=0, minimum-layer residue 4 mod 5
K=1,  R=7,   e=1, minimum-layer residue 3 mod 5
K=6,  R=27,  e=2, minimum-layer residue 3 mod 5
K=31, R=127, e=3, minimum-layer residue 3 mod 5
```

## Post-transient CRT coordinate and all unit assumptions

Since selected primes are larger than (7), none is (5), and

\[
 C_K=5^{b_K}B_K.
\]

Multiplying the global congruence by (2^{b_K}) and reducing modulo (G_K)
gives

\[
 21a_K\equiv68\,10^{b_K}B_KS_K\pmod {G_K}.
\]

Every inverse used by the report is justified:

- (21^{-1}\bmod G_K) exists because selected primes are neither (3) nor (7);
- (10^{-1}\bmod G_K) exists because selected primes exceed (7);
- (B_K^{-1}\bmod G_K) exists because (v_p(Q_K)=1) for every (p\mid G_K);
- (G_K^{-1}\bmod B_K) exists for the same reason; and
- (a_K) is a unit modulo (m_K), since (P_K) is coprime to (Q_K), (Q_K) is
  odd, and multiplication by (2^{b_K}) preserves coprimality.

Thus

\[
 a_KB_K^{-1}10^s
 \equiv {68\over21}10^{b_K+s}S_K\pmod {G_K}.
\]

For

\[
 \alpha_{K,s}\equiv a_KB_K^{-1}10^s\pmod {G_K},\qquad
 \beta_{K,s}\equiv a_KG_K^{-1}10^s\pmod {B_K},
\]

additive CRT gives exactly

\[
 e_{G_KB_K}(a_K10^s)
 =e_{G_K}(\alpha_{K,s})e_{B_K}(\beta_{K,s}).
\]

This is a factorization of one correlated phase, not probabilistic
independence and not a Cartesian decomposition of a real interval.

## Skeleton, localization, and loss after the shift

Let

\[
 u_K\equiv68\,21^{-1}S_K\pmod {G_K},\qquad0\le u_K<G_K.
\]

For an integer (n_K),

\[
 {u_K\over G_K}={n_K\over21}+{68\over21}\Delta_K,
 \qquad
 \Delta_K={S_K\over G_K}
 =\sum_{p\in\mathcal P_K}{\epsilon_p\over p}.
\]

Since every selected prime exceeds (R/2),

\[
 |\Delta_K|< {2\#\mathcal P_K\over R}=O(1/\log R),
\]

using the standard prime-counting bound.  This genuinely localizes the
**unshifted** point near a 21-point grid.  After entering the post-transient
state, however, the only resulting error bound is

\[
 O\!\left({10^{b_K+s}\over\log R}\right).
\]

Because

\[
 10^{b_K}=R^{\log_5 10+o(1)}
 \quad(\log_5 10=1.430676\ldots),
\]

that upper bound is already larger than a constant at (s=0).  Calling it
“vacuous” is correct: it means the available bound no longer localizes the
circle point, not that the actual point is proved far from the grid.  The
Hutton approximation horizon of order (R) does not repair this loss.

## Jacobi identity

Let (h_K) count selected primes congruent to (3\pmod4).  Modulo each selected
(p),

\[
 S_K\equiv\epsilon_p\prod_{q\ne p}q.
\]

Multiplying Legendre symbols, the factors ((\epsilon_p/p)) contribute
((-1)^{h_K}), while quadratic reciprocity over unordered pairs contributes
((-1)^{\binom{h_K}{2}}).  Their product is
((-1)^{h_K(h_K+1)/2}).  The scalar is

\[
 \left({68\cdot21^{-1}\over G_K}\right)
 =\left({68\cdot21\over G_K}\right)
 =\left({4\cdot357\over G_K}\right)
 =\left({357\over G_K}\right),
\]

because a quadratic character equals its inverse and (4) is a square.
Therefore the signs and constant in the report are correct:

\[
 \left({u_K\over G_K}\right)
 =(-1)^{h_K(h_K+1)/2}\left({357\over G_K}\right).
\]

Multiplying by (10^{b_K+s}) gives the stated additional factor
(((10/G_K))^{b_K+s}) for (\alpha_{K,s}).  This is only one quadratic bit; it
does not locate a residue in an archimedean interval.

## Exact (K=3) falsifier

Independent `Fraction` arithmetic gives

```text
R = 15
P = 459056974189868332544096
Q = 146122373360431358535645
G = 11*13 = 143
C = 1021834778744275234515
S = -2
b = 1
B = 204366955748855046903
P mod G = 116
a mod G = 89
u mod G = 48
alpha_(K,0) mod G = 51
21P mod G = 68CS mod G = 5
```

Hence both naive replacements (P_K\equiv u_K\pmod {G_K}) and
(a_K\equiv u_K\pmod {G_K}) are false.  Moreover

```text
10^b B mod G = 124
10^b B mod 11 = 3
10^b B mod 13 = 7
```

and (3) and (7) lie outside the respective subgroups generated by (10).
Thus no decimal-orbit exponent absorbs this omitted multiplier, even locally.

## Reproduction evidence

The supplied checker was run unchanged:

```text
python3 work/ultrapi-resume/hutton_global_crt_check.py

eligible local-prime congruences checked: 10089
global/decomposition/reciprocity check groups: 1743
exact CRT-skeleton phase checks: 4980
all exact checks passed
```

I also ran a separate in-memory Python replay that did not import the supplied
checker.  It independently expanded the Hutton sum with `Fraction`, checked
(v_5(Q_K)) for (K=0,\ldots,90), and for (K=2,\ldots,90) checked all definitions,
1,561 individual local residues, the global congruence, decomposition, every
listed inverse, CRT phases at (s\in\{0,1,2,5,13\}), and the Jacobi identity via
Euler-criterion Legendre symbols.  It reproduced every (K=3) value above.
These runs are `experiment`, not proofs of untested indices.

Focused `git diff --check` also passed for the report and checker.

## Point-in-time hashes

```text
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825  problems/local/pi-digits.txt
b8842721079f84c8a1bd7aa561d7d068f66a5e3e90cf91a2fb1cd52aaf49862c  TheoryLib/PiQuantitativeBlockHitting/T61T61HuttonUpperHalfPrimeSurvival.lean
1b6d22b1dc8fd0e02862a1e0bbe51feb86a3e762923a35cc4a23a02430c48d05  work/ultrapi-resume/t61_independent_audit.md
9b7a834cc5ce9e85af254ce45beb9a48f9c21d41fe4988b357a72799cad4d760  work/ultrapi-resume/hutton_global_crt_attack.md
e8ae5f6c975d55082e2223a30343d955115296c09506bcdd2328fc15e29473a0  work/ultrapi-resume/hutton_global_crt_check.py
```

## Scope

The selected-prime coordinate is now explicit at `proof sketch` status, but
the complementary (B_K)-coordinate remains correlated with it and the only
available grid-localization estimate is destroyed by the mandatory decimal
transient.  Neither the exact identities nor the experiments prove a decimal
cylinder hit for (H_K), let alone for pi.  This is a useful obstruction and a
working stone, not a `candidate resolution` or `verified resolution` of V1.
