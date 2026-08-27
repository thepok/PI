# Hutton selected numerator: global CRT collapse and its scale obstruction

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.  This note follows the fields of
[`problems/TEMPLATE.md`](../../problems/TEMPLATE.md) inside the existing
problem record rather than creating a second problem statement.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained.  The
canonical V1 statement remains a `conjecture`.

Starting from the upper-half-prime valuation and singular-pair structure
formalized in T61, together with the local-residue deduction written out
below, the actual reduced numerator can nevertheless be recombined exactly.
Write the lower Hutton shadow as (H_K=P_K/Q_K) in lowest terms, put
(R=4K+3), and let

\[
 \mathcal P_K=\{p:R/2<p\le R,\ p\text{ prime},\ p>7,\ p\ne17\},
 \qquad G_K=\prod_{p\in\mathcal P_K}p.                  \tag{1}
\]

Define

\[
 \epsilon_p=(-1)^{(p-1)/2},\qquad
 S_K=\sum_{p\in\mathcal P_K}\epsilon_p{G_K\over p},
 \qquad C_K={Q_K\over G_K}.                             \tag{2}
\]

Then the exact global selected-numerator congruence is

\[
 \boxed{\quad21P_K\equiv68C_KS_K\pmod {G_K}.\quad}      \tag{3}
\]

This tracks the factor (Q_K/p=C_K(G_K/p)) that is lost if the local
coordinate (pH_K\pmod p) is treated as the numerator itself.  It yields
three further exact structures.

1. There is an integer (T_K) such that

   \[
   H_K={68\over21}{S_K\over G_K}+{T_K\over21C_K}.        \tag{4}
   \]

   The first summand is an explicit signed reciprocal-prime sum and the
   second has had the entire factor (G_K) stripped from its denominator.
2. If (b_K=v_5(Q_K)), (m_K=Q_K/5^{b_K}=G_KB_K), and

   \[
   a_K\equiv2^{b_K}P_K\pmod {m_K},                       \tag{5}
   \]

   then the canonical additive-CRT coordinate on (G_K) satisfies

   \[
   a_KB_K^{-1}10^s
   \equiv {68\over21}10^{b_K+s}S_K\pmod {G_K}.           \tag{6}
   \]

   Thus the complementary denominator cancels from this one Fourier
   coordinate of the **actual** numerator.
3. The transient is exact:

   \[
   b_K=\lfloor\log_5(4K+3)\rfloor.                       \tag{7}
   \]

Equations (3)--(7), the reciprocity identity below, and their scale analysis
are `proof sketch`: complete elementary derivations are recorded, but they
have not been formalized in Lean.  The local T61 valuation input is
`machine-checked`.  The finite replay is an `experiment`.  The sole external
asymptotic input used here is `literature-checked` as of the date above.
Nothing in this note is a `candidate resolution`.

The useful new invariant is (6).  Its obstruction is equally exact.  The
(G_K)-coordinate is a six-periodic (21)-point skeleton perturbed by
(10^{b_K+s}S_K/G_K).  Prime-counting estimates localize the unshifted
coordinate, but their bound is already vacuous after the mandatory shift
(b_K\asymp\log R), long before the transferable prefix reaches
(s=\Theta(R)).  The other CRT coordinate remains correlated with the same
power (10^s), so a one-factor estimate does not locate the full rational
state in a decimal cylinder.

## 1. Normalized target and notation ambiguity

Write

\[
 \pi=3+\sum_{j\ge0}d_j(\pi)10^{-(j+1)},
 \qquad d_j(\pi)\in\{0,\ldots,9\}.
\]

The canonical statement is

\[
 \forall\ell\ge0\ \forall c<10^\ell\ \exists j\ge0:
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c.       \tag{V1}
\]

The code (c) is padded to length (ell), so leading zeroes count;
occurrence is contiguous; and (ell=0) is vacuous.

There is a notation ambiguity in the surrounding work.  “The numerator
(a_K)” can mean either the numerator of (H_K) in lowest terms or the
post-transient decimal state.  This note uses

\[
 H_K=P_K/Q_K\quad(\gcd(P_K,Q_K)=1)
\]

for the reduced numerator and denominator, and reserves (a_K) for (5).
Both congruences are derived explicitly, so no numerator is silently
substituted for the other.

The named T61 theorems give the first assertion below.  The second assertion
is a `proof sketch` deduction from T61's machine-checked singular-pair
formula, cancellation-factor residue, and regular-term unit facts; no named
Lean theorem currently states that full local coordinate.  Thus, for every
(p\in\mathcal P_K),

\[
 v_p(Q_K)=1,
 \qquad
 pH_K\equiv\epsilon_p{68\over21}\pmod p.                \tag{8}
\]

Indeed, after multiplication by (p), every regular term is zero modulo (p).
The singular pair at exponent (p) becomes

\[
 {4\epsilon_p(2\cdot7^p+3^p)\over3^p7^p}
 \equiv {4\epsilon_p(2\cdot7+3)\over3\cdot7}
 ={68\epsilon_p\over21}\pmod p,
\]

by Fermat's theorem.  Here a rational with (p)-unit denominator is reduced
modulo (p).  The exception (p=17) is genuine and is excluded throughout.

## 2. From every local coordinate to the reduced numerator

Because (p) occurs exactly once in (Q_K), equation (8) means

\[
 {P_K\over Q_K/p}\equiv\epsilon_p{68\over21}\pmod p.
\]

Therefore

\[
 P_K\equiv\epsilon_p{68\over21}{Q_K\over p}
 ={68\over21}C_K\epsilon_p{G_K\over p}\pmod p.          \tag{9}
\]

For a fixed (p\mid G_K), every summand of (S_K) other than the (p)
summand vanishes modulo (p), so

\[
 S_K\equiv\epsilon_p{G_K\over p}\pmod p.                \tag{10}
\]

Equations (9)--(10) give (3) modulo every prime factor of (G_K).  Since
(G_K) is squarefree, the Chinese remainder theorem gives (3) modulo the
whole product.  Notice that (gcd(C_K,G_K)=1); this follows from the exact
exponent-one statement in (8).

The factor (C_K) is essential.  At (K=3), exact arithmetic gives

\[
 G_K=11\cdot13=143,qquad
 P_K\equiv116\pmod {143},                                \tag{11}
\]

whereas the normalized residue
((68/21)S_K\pmod {143}) is (48).  Thus the tempting formula
(P_K\equiv(68/21)S_K\pmod {G_K}) is false.

Define the integer

\[
 T_K={21P_K-68C_KS_K\over G_K}.                          \tag{12}
\]

Dividing (12) by (21C_KG_K=21Q_K) gives the exact
archimedean decomposition (4).  If

\[
 \Delta_K={S_K\over G_K}
 =\sum_{p\in\mathcal P_K}{\epsilon_p\over p},            \tag{13}
\]

then the Hutton bracket and (4) give

\[
 \left|\pi-{T_K\over21C_K}\right|
 \le W_K+{68\over21}|\Delta_K|,                          \tag{14}
\]

where

\[
 W_K={8\over(4K+5)3^{4K+5}}
     +{4\over(4K+5)7^{4K+5}}.                            \tag{15}
\]

Every selected prime exceeds (R/2), hence, without any cancellation,

\[
 |\Delta_K|
 \le\sum_{p\in\mathcal P_K}{1\over p}
 <{2\#\mathcal P_K\over R}=O(1/\log R).                 \tag{16}
\]

Thus (4) really does strip an exponentially large squarefree factor while
leaving a rational that approaches pi, but only at inverse-logarithmic
speed.  Multiplication by (10^{\Theta(R)}) destroys the usefulness of
(14).  It is not a moving-digit approximation.

## 3. The exact actual-state coordinate

Since no selected prime is (5), write

\[
 Q_K=5^{b_K}m_K=5^{b_K}G_KB_K,
 \qquad C_K=5^{b_K}B_K.                                 \tag{17}
\]

Multiplying (3) by (2^{b_K}) and using (5) gives

\[
 21a_K\equiv68\,10^{b_K}B_KS_K\pmod {G_K}.              \tag{18}
\]

Both (21) and (B_K) are units modulo (G_K), so (18) is precisely (6).
This is stronger than a collection of unrelated local residues: it is the
global coefficient appearing in the canonical additive CRT factorization.

Put (e_M(x)=\exp(2\pi i x/M)), and define

\[
 \alpha_{K,s}\equiv a_KB_K^{-1}10^s\pmod {G_K},
 \qquad
 \beta_{K,s}\equiv a_KG_K^{-1}10^s\pmod {B_K}.          \tag{19}
\]

Then, exactly,

\[
 e_{m_K}(a_K10^s)
 =e_{G_K}(\alpha_{K,s})e_{B_K}(\beta_{K,s}),             \tag{20}
\]

and (6) determines the first coefficient:

\[
 \alpha_{K,s}\equiv {68\over21}10^{b_K+s}S_K
 \pmod {G_K}.                                           \tag{21}
\]

This cancellation of (B_K) is the main usable invariant of the attack.
It does **not** say that the ordinary residue (a_K\pmod {G_K}) equals the
right side: the additive CRT inverse (B_K^{-1}) matters.  At (K=3),

\[
 a_K\equiv89\pmod {143},\qquad
 (68/21)S_K\equiv48\pmod {143}.                          \tag{22}
\]

Nor can the missing multiplier simply be absorbed by shifting the decimal
orbit.  At the same (K), (10^{b_K}B_K) is congruent to (3pmod {11})
and (7pmod {13}), and lies outside the subgroup generated by (10) in
both prime fields.  No exponent shift realizes this multiplier even
locally, hence none does so modulo (G_K).

Finally, (20) is a product of two correlated phases, not a product of two
independent random variables.  Cancellation or interval coverage in its
(G_K) factor can be undone by the (B_K) factor.  A real interval in
\(\mathbb Z/(G_KB_K)\mathbb Z\) is not a Cartesian product of local
intervals.

## 4. A 21-point skeleton and the exact transient obstruction

Let (u_K) be the least residue satisfying

\[
 u_K\equiv68\,21^{-1}S_K\pmod {G_K},qquad0\le u_K<G_K.
\]

There is an integer (n_K) for which

\[
 21u_K=68S_K+n_KG_K,qquad
 {u_K\over G_K}={n_K\over21}+{68\over21}\Delta_K.       \tag{23}
\]

Consequently (21) has the exact circle identity

\[
 {\alpha_{K,s}\over G_K}
 \equiv {n_K10^{b_K+s}\over21}
       +{68\over21}10^{b_K+s}\Delta_K\pmod1.            \tag{24}
\]

Since

\[
 10,16,13,4,19,1\pmod {21}                              \tag{25}
\]

are the successive powers of (10), the first term of (24) is periodic
with period dividing six.  Equation (16) puts the unshifted (u_K/G_K)
within (O(1/\log R)) of the (21)-point grid.

The five-adic transient can be evaluated exactly.  Rewrite the Hutton sum by
odd exponent (r\le R):

\[
 H_K=\sum_{\substack{1\le r\le R\\r\text{ odd}}}
 {4\epsilon_r(2\cdot7^r+3^r)\over r3^r7^r}.             \tag{26}
\]

For odd (r), the factor (2\cdot7^r+3^r) is congruent to (2) or (3)
modulo (5), according as (r\equiv1) or (3\pmod4); it is always a
5-unit.  Put (e=\lfloor\log_5R\rfloor) and (L=5^e).  Since
(R<5L), the terms of minimal 5-adic valuation are exactly

\[
 r=L,
 \quad\text{and, if }3L\le R,\quad r=3L.                \tag{27}
\]

After multiplication by (5^e), their residues modulo (5) are
respectively (3) and (1).  The minimum layer therefore sums to (3) or
(4), never zero.  All other terms have larger valuation.  Hence

\[
 v_5(H_K)=-e,
 \qquad v_5(Q_K)=e,                                     \tag{28}
\]

which is (7), including (K=0).

This shows exactly why the skeleton does not yet localize a transferable
post-transient state.  From (16), the available bound in (24) is useful only
while

\[
 10^{b_K+s}=o(\log R).                                  \tag{29}
\]

But already

\[
 10^{b_K}=R^{\log_5 10+o(1)}
          =R^{1.430676\ldots+o(1)},                      \tag{30}
\]

so the absolute prime-counting bound is vacuous at (s=0).  The Hutton
bracket transfers (\Theta(R)) decimal positions.  Controlling (24) over
that range would require fine information about

\[
 \left\{10^{b_K+s}\sum_{p\in\mathcal P_K}{\epsilon_p\over p}\right\},
 \qquad 0\le s\le\Theta(R),                              \tag{31}
\]

not merely the small unscaled value of the signed sum.  Equation (31) is a
newly isolated moving-residue problem, not a consequence of the prime number
theorem.

## 5. Reciprocity gives one global character, not a location

Although Wilson's theorem does not evaluate the sparse moving products
(G_K/p\pmod p), quadratic reciprocity does collapse their total Jacobi
symbol.  Let

\[
 h_K=\#\{p\in\mathcal P_K:p\equiv3\pmod4\}.
\]

Then

\[
 \boxed{
 \left({u_K\over G_K}\right)
 =(-1)^{h_K(h_K+1)/2}\left({357\over G_K}\right).
 }                                                        \tag{32}
\]

Indeed, modulo (p),

\[
 S_K\equiv\epsilon_p\prod_{q\in\mathcal P_K,\,q\ne p}q.
\]

The product of ((\epsilon_p/p)) contributes ((-1)^{h_K}).  Pairing
((q/p)(p/q)) over unordered prime pairs contributes
((-1)^{\binom{h_K}{2}}).  Finally
((68\cdot21^{-1}/p)=(357/p)).  Multiplication gives (32).

Along the actual (G_K)-coordinate this becomes

\[
 \left({\alpha_{K,s}\over G_K}\right)
 =\left({10\over G_K}\right)^{b_K+s}
  (-1)^{h_K(h_K+1)/2}\left({357\over G_K}\right).       \tag{33}
\]

This is an exact global invariant, but it supplies only one quadratic bit.
It does not choose an archimedean interval among the (G_K) residues, and it
does not control the (B_K) phase in (20).

There is no comparable Wilson simplification in the additive residue found
here.  Wilson evaluates a complete nonzero residue system modulo one prime;
(G_K/p) is the product of a sparse set of other primes in a moving real
interval.  The exact replay falsifies two natural coarse replacements:

- the lift branch (n_K\pmod {21}) is not determined by (R\pmod {84}):
  (K=2) and (K=23) both have (R\equiv11\pmod {84}), but their branches
  are (10) and (4) modulo (21);
- even the sign of (Delta_K) changes: it is negative at (K=10) and
  positive at (K=12).

These counterexamples do not rule out a subtler prime-product theorem, but
they reject the simple periodic formulae that would make (24) automatic.

## 6. Exact replay and finite falsification

The companion checker is
[`hutton_global_crt_check.py`](hutton_global_crt_check.py).  It uses only
integers and `Fraction` arithmetic for every assertion.  Run it from the
repository root:

```text
python3 work/ultrapi-resume/hutton_global_crt_check.py
```

The 2026-08-12 run reported:

```text
source sha256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
eligible local-prime congruences checked: 10089
global/decomposition/reciprocity check groups: 1743
exact CRT-skeleton phase checks: 4980
falsified naive formulas at K=3:
  P mod G = 116 ; a mod G = 89 ; normalized u = 48
  complement multiplier is outside <10> at primes: [11, 13]
same R mod 84 but different lift branch:
  K=2 -> 10 mod 21; K=23 -> 4 mod 21
sample rows: K R #P b branch delta dist(u,grid) dist(shifted,grid) Jacobi
    3   15   2  1  8 -1.39860140e-02 2.33100233e-03 2.33100233e-02 +1
   10   43   6  2 16 -1.30921098e-02 5.22554925e-03 1.25459835e-03 +1
   12   51   6  2  4 +9.10955534e-03 1.81214399e-02 2.62017696e-03 +1
   20   83  10  2 11 -6.62378657e-02 2.36107204e-02 1.98803375e-02 +1
   40  163  16  3  5 +3.28814013e-03 1.06473109e-02 1.93557784e-02 -1
   80  323  29  3  2 -8.35554060e-03 2.05630114e-02 8.41718557e-03 +1
  120  483  39  3 18 +3.40754943e-03 1.10339696e-02 1.36494501e-02 -1
  200  803  60  4 19 -5.21137165e-03 1.68749177e-02 1.27276819e-02 -1
G-factor-only two-digit coverage: K starts distinct-cells
  20 38 30
  40 75 53
  80 152 76
  120 228 89
  200 380 99
all exact checks passed
```

For every (2\le K\le250), the checker independently expands the complete
rational Hutton sum and verifies:

- every local congruence (8) and the exact quotient
  (Q_K/p=C_K(G_K/p));
- the global congruence (3), decomposition (4), and
  (gcd(S_K,G_K)=1);
- the exact transient (7);
- twenty additive-CRT and skeleton identities per (K);
- the Jacobi identity (32); and
- the exact finite bound in (16).

The last five coverage rows concern only the (G_K) factor in (20).  They
are an `experiment`, not decimal-cylinder certificates for (H_K), because
they omit the correlated (B_K) coordinate.  The numerical distances and
all untested extrapolations likewise have only `experiment` status.

Point-in-time checker SHA-256 after this run:

```text
e8ae5f6c975d55082e2223a30343d955115296c09506bcdd2328fc15e29473a0  work/ultrapi-resume/hutton_global_crt_check.py
```

## 7. Source and literature audit

The local input is T61,
[`T61T61HuttonUpperHalfPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T61T61HuttonUpperHalfPrimeSurvival.lean),
point-in-time SHA-256
`b8842721079f84c8a1bd7aa561d7d068f66a5e3e90cf91a2fb1cd52aaf49862c`.
Its independent audit is
[`t61_independent_audit.md`](t61_independent_audit.md), point-in-time
SHA-256
`1b6d22b1dc8fd0e02862a1e0bbe51feb86a3e762923a35cc4a23a02430c48d05`.
Those files supply the `machine-checked` exponent-one input and the
machine-checked ingredients for the local-residue calculation.  The full
local congruence (8), and hence the CRT derivation depending on it, retain
`proof sketch` status because no audited Lean declaration currently states
that congruence.

A bounded primary-source check was performed on **2026-08-12 UTC** because a
concrete prime-counting theorem applies to (16).  Broadbent--Kadiri--Lumley--
Ng--Wilk,
[*Sharper Bounds for the Chebyshev function*](https://arxiv.org/abs/2002.11068),
gives explicit bounds for (θ(x)-x) much stronger than the
(\pi(x)=O(x/\log x)) consequence used here.  No equidistribution,
prime-product, or decimal-orbit conclusion is attributed to that source.

Quadratic reciprocity, additive CRT, and the 5-adic calculation are elementary
ingredients written out above.  No source or novelty claim is needed for
them.  The earlier
[`hutton_prefix_sum_attack.md`](hutton_prefix_sum_attack.md) contains the
dated primary-source audit for incomplete Korobov estimates and explains why
known results do not cover the logarithmic-length actual-numerator prefix.
No new primary theorem was found or invoked that controls the coupled phase
in (20) at (s=\Theta(R)).

## 8. What remains

The global numerator is no longer locally mysterious on the selected
squarefree factor: equations (3), (6), (24), and (32) determine it exactly.
A continuation must now control one of two genuinely global objects.

1. Prove a joint estimate for

   \[
   e_{G_K}\!\left({68\over21}10^{b_K+s}S_K\right)
   e_{B_K}(\beta_{K,s}),\qquad 0\le s\le\Theta(R),       \tag{34}
   \]

   retaining the correlation between its two factors; or
2. directly show that some full residues (a_K10^s\pmod {m_K}) enter every
   fixed decimal cylinder inside the Hutton transfer horizon.

The second statement is the missing localized block theorem and, together
with the exact bracket, would imply V1.  The first is not supplied by the
smallness of (Delta_K), its quadratic character, the length of the complete
orbit, or coverage of the isolated (G_K) factor.

**Bottom line:** the local residues deduced from T61's machine-checked
ingredients admit a clean global recombination at `proof sketch` status.
The upper-half-prime part of the actual numerator is an explicit signed
reciprocal-prime phase with a six-periodic 21-grid skeleton.  That is a real
working stone.  The exact five-adic transient and the correlated complement
show why it is not yet a decimal-block theorem: the available localization
covers only a negligible initial segment and does not reach the
post-transient (O(K)) orbit.  No complete proof of V1 follows.
