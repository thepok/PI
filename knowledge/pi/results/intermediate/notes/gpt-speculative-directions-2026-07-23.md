# Speculative research directions (GPT-5.6 Pro, 2026-07-23, via Marcel)

Status: UNVERIFIED external proposals, preserved for item authors. The
coordinator hand-verified two core mathematical claims (sparse-witness
criterion, period-p gap inequality) — both correct. All literature
references are UNVERIFIED until pinned; the "July 2026 preprints" cited in
Direction 2 may not exist. Compact triage: work/theory/SUGGESTIONS.md.

## Strategic reset: sparse witness energy (verified correct)

The frontal collision bound R_pi(m,N) <= C_s(N + N^2 10^{-sm}) targets C1
(positive density of every word) — strategically excessive for the root
question V1 (one occurrence per word). Weaker criterion: for finite
S subset N, E_{pi,S}(m) = #{(i,j) in S^2 : B_pi(i,m) = B_pi(j,m)},
D_{pi,S}(m) = #distinct sampled blocks. Cauchy–Schwarz: D >= |S|^2 / E.
For w in D^k let L_w(m) = #length-m words avoiding w; U_k(m) = max_w L_w(m)
(exactly computable via the KMP/de Bruijn automaton — transfer-matrix tech
the library already has). Then:

    |S|^2 / E_{pi,S}(m) > U_k(m)  ==>  every length-k word occurs in pi.

(If w were missing, every sampled m-block lies in its avoider language, so
D <= L_w(m) <= U_k(m).) Asymptotic version: limsup_m (1/m) log10 of the
sup over finite S of |S|^2/E = 1 implies pi disjunctive. Needs only chosen
block lengths m, chosen sparse positions S, one favorable finite witness
per k — no consecutive prefixes, no density. Should REPLACE the current
collision bound as the most permissive collision route to V1.

## Direction 1 (fund first): formula-aligned endpoint blocks + p-adic state dynamics

Take a certified fast formula for pi (Chudnovsky, Machin, Ramanujan–Sato,
AGM), approximants a_n; choose lambda strictly below digits-gained-per-step,
L_n = lambda*n (linear guard region); u_{n,m} = floor(10^{L_n} pi) mod 10^m
becomes, via certified interval arithmetic, an EXACT arithmetic function of
the finite formula state. Targets (either suffices): #{u_{n,m} : n in I_m}
> U_k(m) (via sparse-witness => every length-k word occurs), or
#{u_{n,m}} = 10^{m-o(m)} (=> disjunctivity). Attack: recurrences for the
formula state mod 2^m and 5^m (normalized valuations), CRT-combined;
1-Lipschitz p-adic transitivity criteria; Ramanujan–Sato supercongruence
frameworks as actual p-adic identities. Kill criteria (computational,
BEFORE proof effort): image growth c^m with c<10; short p-adic cycles;
state dimension growing with m (no bounded-dimensional recurrence — this
is the central technical risk and the make-or-break question).

## Direction 2: pi-specific steering word + Subspace Theorem (VERIFY SOURCES FIRST)

Claimed July 2026 preprints: superlinear complexity of the (3/2)^n steering
word via an exact repetition identity + Subspace Theorem; binary digits of
3^m via periodic-window linear forms in logs (Baker–Wüstholz). UNVERIFIED —
pin or discard before any work. Lesson if real: recode a pi algorithm as an
algebraic rounding system, attack the carry/steering itinerary, not the
decimal orbit. First deliverable: an exact repetition identity with
controlled arithmetic height (without it, kill — hypergeometric recurrences
have unbounded new primes, AGM grows algebraic degree; the fixed
finitely-generated-group framework may not survive).

## Direction 3: forbidden-word lacunary polynomial family

If w never occurs, pi lives in the survivor set of T(x)=10x mod 1 with the
w-cylinder removed (explicit automaton-recognized Cantor set). Product of
cylinder-avoiding test functions expands to a lacunary polynomial family
P_{w,N}(pi) with automaton-constrained frequencies (bounded coefficients
times powers of 10), transfer-matrix factorization, spectral-radius decay.
Missing w makes pi an exponentially exceptional point of this SPECIFIC
recursive family (vs. Weyl's arbitrary fixed frequency). First theorem: a
lossless transfer-matrix representation; then hunt identities connecting
P_{w,N}(pi) to Chudnovsky/arctan/BBP states BEFORE absolute values. Kill:
if every representation has exponential l^1-norm, triangle inequality
destroys all Diophantine input (repackaged wall).

## Direction 4: collision-graph inverse theorem

Graph G_m on positions, i~j iff blocks equal, edge label r=j-i; equal
blocks give ||10^i(10^r-1)pi|| < 10^{-m}. Program: regularize high-energy
collision graphs (BSG, dependent random choice, entropy decrement),
extract repeated lag patterns/additive structure, COMBINE near-return
relations before invoking Diophantine approximation; exploit
10^{r+s}-1 = (10^r-1) + 10^r(10^s-1), gcd(10^r-1,10^s-1)=10^{gcd(r,s)}-1.
WARNING (falsifier discipline): "high energy or missing word forces long
periodic stretches" is FALSE for mixing proper subshifts — test every
candidate lemma against Markov samples from one-word-forbidden subshifts;
valid inverse theorems must use energy above the subshift equilibrium,
cross-scale coherence, higher-order tensors, or arithmetic of the
coefficients 10^i(10^r-1).

## Direction 5: carry-controlled base transfer + BBP joining

5A: quantitative carry-transfer theorem: base-16 local min-entropy h +
bounded carry-sensitive tails c(n) => explicit decimal factor entropy
F(h,c). Guard digits unbounded only near decimal boundaries = restricted
rational-approximation condition. Needs blockwise min-entropy,
anti-concentration at conversion boundaries, carry-chain bounds — useful
combinatorics independent of pi. 5B: exact joining
BBP state -> hex digits -> decimal carry state -> decimal digits with a
conditional-entropy inequality; milestone is an exact finite-entropy
joining/factor map, NOT Furstenberg-by-analogy (invariant measures with
large Fourier coefficients along powers block generic rigidity arguments).

## Direction 6 (moonshot lane): restricted-numerator irrationality measures

If pi avoids w, floor(10^n pi) lies in the avoider set A_w(n),
|A_w(n)| ~ rho_w^n < 10^n. Target: min over a in A_w(n) of |pi - a/10^n|
beating 10^{-n} at ONE n proves the prefix is not in the avoider language.
Need automaton-compressed polynomials/determinants of degree O(n)-O(n^2)
that are tiny on the survivor Cantor set, contradicting known quantitative
approximation properties of pi. Feasibility audit FIRST: degree D_n, height
H_n, survivor-set bound, available |P(pi)| lower bound as f(D,H); if lower
bound ~ exp[-D^c log H] vs automaton's exp[-cD], dead.

## Direction 7 (attainable, unconditional — do early): period-p gap principle

(Verified correct.) A period-p window starting after a digits, length L,
gives a rational with denominator dividing 10^a(10^p-1) and error
O(10^{-(a+L)}); mu' > mu(pi) forces L <= (mu'-1)a + mu'p + O(1) beyond a
finite onset. Generalizes the digit-change chain (pi-digits T14/T18) from
period 1 to every fixed p; geometric windows force log-many period-p
breaks; aim for uniformity p <= c log N. Will NOT prove disjunctivity
(Sturmian countermodels) — value is a new unconditional hierarchy + input
to collision inverse structure.

## Direction 8: semigroup of several formulas (extension of 1)

Multiple Ramanujan–Sato/Machin/AGM representations with different
denominator prime structure and p-adic behavior; transition maps F_r on
modular states; the GENERATED SEMIGROUP may act transitively mod 2^m, 5^m
even if no single map does; pool endpoint positions into S. Decisive
computation: the generated transition semigroup mod small 2^m/5^m — full
transitive group = something to prove; shared invariant congruence classes
= fiction, kill.

## Deprioritize (all consistent with our own audits)

Fixed-pi Poisson pair correlation as next target (no arithmetic hook —
matches our C3 wall assessment); full Weyl cancellation (normality-grade
machinery for a density-grade need); improving the generic irrationality
exponent (scale mismatch is structural — matches [block-density T24]);
more conventional digit statistics at 10^7-10^8 digits (already inside
random-control ranges — experiments should instead probe PROOF OBJECTS:
endpoint-block images, modular cycles, automaton polynomial values,
collision-graph coherence, carry chains, generated semigroups).

## Recommended order of attack (GPT's, endorsed by coordinator with caveats)

1. Formalize sparse-witness energy + exact automaton U_k(m).
2. Compute formula-aligned endpoint blocks; inspect image growth/collision
   energy mod 2^m, 5^m, 10^m.
3. Bounded-dimensional modular recurrence attempt (make-or-break).
4. In parallel: period-p gap principle (attainable, unconditional).
5. Collision-graph inverse only after subshift stress-testing.
6. Restricted-language transcendence = moonshot lane.
