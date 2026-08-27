# Speculative directions, second memo (GPT-5.6 Pro, 2026-07-23, via Marcel)

Status: UNVERIFIED external proposals. Coordinator hand-verified the core
covering argument of Direction 1 (correct) and the carry-relation schema of
Direction 2 (correct). Headline critique adopted: do not generate cosmetic
variants of the same collision estimate — change the object being estimated.

## Direction 1 (STRONGEST): quantitative Furstenberg transversal — VERIFIED

K_pi = closure{10^n pi mod 1}. b=16 (mult. independent of 10; BBP structure).
M_b(eps) = min M such that union_{m<=M} T_16^m K_pi is eps-dense in T.
Furstenberg: {10^n 16^m pi} dense (pi irrational) => M_b(eps) < infinity
UNCONDITIONALLY. Missing word w => K_pi in subshift K_w with box dim
d_w <= (1/k)log10(10^k - 1) < 1 (system's T32 entropy machinery). Covering:
N_eps(union T_16^m K) << eps^{-d} 16^{Md}; eps-density needs >> eps^{-1};
hence M >= ((1-d_w)/(d_w log 16)) log(1/eps) - O(1). Therefore:

    M_16(eps) = o(log(1/eps))  ==>  dim K_pi = 1  ==>  V1 (disjunctivity).

Word-specific: liminf M_16(eps)/log(1/eps) < (1-d_w)/(d_w log 16) already
certifies occurrence of w. FIRST FORMAL ARTIFACTS (kernel-checkable NOW,
no Furstenberg needed for the reduction itself): (i) general theorem —
closed T_10-invariant K with sublog 16-transversal width is all of T;
(ii) the word-specific quantitative bound via the covering argument.
New ladder rung: sublog 10-16 transversal => V1, asking far less than Weyl.

## Direction 2: exact carry automata for the 10-16 transversal — schema VERIFIED

Multiplication by 16 in decimal: bounded-carry relation 16 x_j + c_{j+1} =
y_j + 10 c_j, 0 <= c_j <= 15. Compose KMP automaton (avoid w) x carry
transducer, minimize: T_16^m K_w is sofic; so is Y_{w,M} = union. Define
tau_w(ell) = min M with L_ell(Y_{w,M}) = all length-ell decimal words.
Expected: tau_w(ell) >= c_w ell - O(1) (symbolic covering bound); exact
automata may give explicit omitted-word certificates. EVERYTHING FINITE
AND CERTIFIABLE — ideal for this system (transducers, products, language
inclusion, rational Perron bounds, Lean correspondence to real x16).
IMMEDIATE EXPERIMENT: tau_w(ell) for |w| in 1..4, ell <= 30; classify
growth (linear validates the framework; bounded/log would upend strategy).

## Direction 3: thin rectangular exponential sums

S_{N,M}(h) = sum_{n<N, m<M} e(h 10^n 16^m pi). Sufficient certificate:
for every eps exists M = o(log(1/eps)), N, H ~ 1/eps with
max_{|h|<=H} |S_{N,M}(h)| <= eta(eps) NM -> Erdos-Turan gives eps-density
of the thin rectangle -> Direction 1 -> V1. Rewrite as average cancellation
over the sparse frequency family h*16^m — averaging is exploitable
(large sieve, bilinear, entropy increment) where fixed-frequency Weyl is
not. First artifact: formal chain thin-ET certificate => M_16 sublog => V1.

## Direction 4: certified approximants' full modular orbits

a_r = P_r/Q_r with |pi - a_r| <= 10^{-L_r}: for n <= L_r - k - s, blocks of
{10^n a_r} = {P_r 10^n / Q_r} transfer to pi with safety margin; after
removing 2,5 from Q_r this is a geometric progression mod Q_r'. Finite
target: first L_r-k-s elements of P_r 10^n mod Q_r' robustly hit all
k-cylinders; Fourier version = incomplete exponential sums over geometric
progressions (real literature exists). MANDATORY AUDIT before proof work:
L_r, log Q_r', ord_{Q_r'}(10), factorization profile, ratio L_r/log Q_r';
kill if ratio -> 0, tiny orders, or estimates need segments poly(Q_r').

## Directions 5-9 (moonshot lane; see full text below)

5: CM/Hecke steering of endpoint blocks — first milestone is whether ANY
Ramanujan-Sato supercongruence relates real truncation error to the
approximation mod 2^k AND mod 5^k (most are same-prime p-adic analogues —
if no bridge, dead). 6: regular-language irrationality measure — coherent
family A_n = floor(10^n pi) in one automaton language + pi-specific
analytic identity (sin pi = 0, period ODEs); NON-NEGOTIABLE check: if the
proof survives deleting the pi-identity, it is bogus (transcendentals
exist in every proper subshift); need Lambda_N ~ e^{-cN^2} vs analytic
e^{-CN log N} — an e^{-CN} gain reproduces the known scale mismatch.
7: fractal uncertainty principle extended to regular languages —
||1_{A_w(m)} F 1_{B_w(m)}|| <= 10^{-beta_w m}; kill if no explicit dual
set B_w(m) or the frequency set has subgroup structure. 8: random-order
2/5 carry paths (binom(2n,n) orders all ending at 10^n pi) — bridge
operator B_n over guarded transducer products; endpoint concentration vs
generic carry mixing dichotomy; abandon if commutation makes B_n
tautologically rank-deficient. 9: overproduced approximants near the
forbidden Cantor set vs rational-points-in-missing-digit-sets counting —
low probability; compare exponents first.

## Recommended queue (author's, endorsed)

1. Formalize the quantitative transversal theorem (+ word-specific bound).
2. Build/certify the decimal x16 carry transducer.
3. Compute tau_w(ell) for all short w.
4. Formalize thin-rectangular-ET => V1 chain.
5. Audit exact formulas: L_r, Q_r', ord_{Q_r'}(10).
6. Only then: CM / determinant / FUP lanes.

Best combined program: Furstenberg thin transversal + exact carry automata
+ joint 10-16 discrepancy — starts from an unconditional density theorem
for a richer orbit and asks how cheaply the auxiliary direction is removed.
