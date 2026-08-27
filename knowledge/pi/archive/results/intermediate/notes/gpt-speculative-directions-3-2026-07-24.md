# Speculative directions, third memo: rigidity amplifiers (GPT-5.6 Pro, 2026-07-24, via Marcel)

Status: UNVERIFIED external proposals; coordinator hand-verified the
overlap-rigidity reduction (Direction 1) and the many-anchor covering chain
(Direction 5, modulo the exact discrepancy exponent, to be pinned).
Rudolph–Johnson and Huang rigidity theorems are real but MUST be
source-pinned before items rely on them. Strategy: prove a WEAK statistical
property of one orbit measure, let a rigidity theorem amplify to Lebesgue.

## 1 (VERIFIED, top priority): multiplicative overlap rigidity => V1

T = x10 on the circle, X_pi the orbit closure, q mult. independent of 10
(useful: 9, 11, 16 — shift-subtract, shift-add, BBP-aligned). THEOREM: if
an ergodic T-invariant mu has supp(mu) in X_pi, h_mu(T) > 0, and mu is NOT
mutually singular with (T_q)_* mu, then mu = (T_q)_* mu (commuting
pushforward is ergodic; distinct ergodic measures are mutually singular),
so mu is x10- and xq-invariant with positive entropy, so Rudolph–Johnson
gives mu = Lebesgue, so X_pi = T and pi is disjunctive. FINITE-BLOCK
SUFFICIENT CRITERION: a subsequence of empirical measures with (i) an
ergodic weak limit, (ii) Renyi-2 cylinder bound sum_w p^2 <= C 10^{-eta m}
(positive entropy), (iii) overlap coefficient Omega_q(m, N_j) =
sum_w min(p, p^{(q)}) bounded below uniformly in m (prevents
singularity). Much weaker than collision decay: one subsequence, one
positive eta, no s->1, no all-N uniformity, no per-word density. Items:
formalize the rigidity reduction (Rudolph–Johnson as pinned hypothesis);
formalize the empirical criterion; pin Rudolph 1990 / Johnson 1992.

## 5 (VERIFIED in structure): many-anchor incidence theorem

Pinned mu(pi) <= 7.1032 gives rotation discrepancy D_Q({q pi}) << Q^{-theta}
(theta from the pinned bound via Erdos–Turan; EXACT exponent to be pinned —
memo uses theta < 1/mu ~ 0.1408, the standard 1/(mu-1) form is even
better). If dim_box X_pi <= d' < 1, cover by eps^{-d'} intervals:
I(Q,eps)/Q << eps^{1-d'} + eps^{-d'} Q^{-theta}. With eps = Q^{-a},
a < theta, both vanish. THEOREM: positive-proportion anchors —
limsup I(Q, Q^{-a})/Q > 0 for some a < theta — forces dim X_pi = 1, hence
V1. (Anchor: q with dist(q pi, X_pi) < eps, e.g. ||(10^n - q) pi|| < eps.)
Finite version I(Q,eps;N) stated. Weaker incidence I >= Q^{1-gamma} gives
an UNCONDITIONAL dimension lower bound dim >= 1 - gamma/theta after
optimizing — an incidence-to-entropy ladder from the pinned bound alone.
Elementary; formalizable now.

## 3: exact entropy-gap program (finite, start immediately)

Y_{w,q} = K_w intersect T_q^{-1} K_w via carry-transducer x KMP
composition (two-sided natural extension; carry direction is the easy
mistake — formalize the correspondence first). Claim: unique positive-
entropy MME on K_w + rigidity => h_top(Y_{w,q}) < h_top(K_w) strictly.
Compute Delta_{w,q} and Gamma_k(q) = min_w Delta for k <= 6,
q in {2,3,9,11,16,99,101} — Perron roots of integer matrices, exact
algebraic certificates; selects the best multiplier for arithmetic
investment.

## 7: Perron–Frobenius martingale witness (strengthens the pincer)

For forbidden w with Perron root rho_w < 10 and right eigenvector r:
P_w(s,d) = r_{s'}/(rho_w r_s) is a Markov kernel; along ANY avoiding path
the likelihood ratio vs uniform is (10/rho_w)^N r_{s_N}/r_{s_0}. So a
missing word gives g_w with sum_{n<N} g_w(T^n pi) = N log(10/rho_w) +
O_w(1) FOR EVERY N — exact all-time linear drift, not subsequence
resonance; Fourier expansion has explicit algebraic coefficients from the
automaton. Items: PF betting formalization, algebraic certificates for
rho_w, r, all-N drift identity, boundary-robust truncation, and the
retention-vs-escape dichotomy (route dead only if the drift provably
escapes to frequencies >> 10^k — demonstrate, don't assume).

## 2: moving multipliers q_r = 10^r + l (Huang rigidity — PIN FIRST)

x(10^r+1) = shift-add with carries — exactly the campaign's lag parameter.
Huang: non-atomic strongly mixing xp-invariant mu invariant under
sufficiently many p^r + l multipliers is Lebesgue (three variants:
ergodic/density-one, weak-mixing/positive-density, strong-mixing/
infinitely-many). Moving-overlap criterion: infinitely many r with
inf_m cylinder-overlap of mu and (T_{10^r+l})_* mu > 0 => mu Lebesgue =>
V1. Requires pinning Huang's paper and exact hypotheses.

## 4: CRT entropy split. log10 - h(D) = (log2 - h(D mod 2)) +
(log5 - h(D mod 5)) + I(A;B): any decimal defect is a 2-marginal defect,
a 5-marginal defect, or persistent cross-prime dependence. Exact-cycle
route: single-cycle (Anashin-ergodic) formula states mod every 2^m and
5^m with COPRIME cycle lengths give exact CRT coverage of all decimal
blocks — no probabilistic independence needed. Kill: growing state
dimension, output collapse, short cycles.

## 6, 8, 9, 10 (second tier / moonshots — see kill criteria in text):

6 representation amplifiers (many distinct anchors from exact-identity
transformations; kill if all branches share precision schedules or
anchors only polylog(Q)); 8 shift-add convolution entropy (needs
graph-to-product TV bound at scale m ~ r — beyond ordinary mixing);
9 Pisot-base (beta = 1+sqrt3 BBP) toral lift — first deliverable is a
correct rigidity theorem for <10 I_d, A_beta>, noninvertibility is a real
gap, NO digit computation before that; 10 Mahler/G-function
incompatibility — complexity-floor lane only, not a V1 route.

## Recommended queue (author's, endorsed with pin-first caveats)

1. Formalize overlap rigidity (+ empirical criterion; pin Rudolph–Johnson).
2. Formalize many-anchor incidence (pin the discrepancy theorem + exponent).
3. Carry automata for q = 9, 11, 16; compute Delta_{w,q}, Gamma_k(q).
4. 2-adic/5-adic exact-cycle search on formula states.
5. PF martingale witness.
6. Representation amplifiers. Moonshots after.

Author's core claim, endorsed: the collision program tries to prove almost
everything directly; these routes ask for substantially less and outsource
the final jump to rigid theorems.
