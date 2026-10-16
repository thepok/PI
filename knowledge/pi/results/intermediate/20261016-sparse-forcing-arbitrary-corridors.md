# Arbitrary sparse corridors in a long-word avoidance shift

Claim status: `proof sketch`. Date: 2026-10-16.

This extends the scope of the existing [fixed-word full-dimension proof sketch](20260905-fixed-word-full-dimension.md). That note prescribes specially guarded ALA packets. The construction below handles **every compatible assignment on every fixed zero-density position set**, including packets that cannot be emitted by an unconditioned forward Parry process.

The conclusion is a proper-SFT subclass of P1′. It is neither a claim about the digits of pi nor a universal P1/P1′ resolution. No Lean verification or novelty claim is made.

## Statement

Fix a decimal word w of length m >= 49. Let Sigma_w be its one-sided avoidance SFT and d_w = log_10(lambda), where lambda is the Perron root of the canonical prefix automaton. Let F be any subset of the positive integers with

    f(N) = |F intersect [1,N]| = o(N).

For each assignment a:F->{0,...,9} for which (Sigma_w)_a is nonempty, put K_a = pi_10((Sigma_w)_a). Then

    for every 0 < s < d_w there exists kappa = kappa(w,F,s) > 0
    such that, for every compatible assignment a on F,
        dim_H(K_a intersect BA(kappa)) > s.                     (A)

In particular dim_H(K_a intersect BA) = d_w for every such assignment. Entropy neutrality need not be assumed: the construction itself also proves dim_H(K_a)=d_w.

The order of quantifiers is part of the result. One kappa works for all compatible assignments on the fixed F and at every decimal depth. It may change when s changes. Ordinary P1′ follows for this family of proper SFTs by taking F to be the union of the prescribed packet positions.

## Inputs retained from the earlier proof sketch

Let D be the digit-counting matrix of the m-state prefix automaton, H=diag(h), and normalize h_0=1. Set B_0=10^m and

    P = lambda^(-m) H^(-1) D^m H.

The earlier word-automaton estimates, valid for every m >= 2, give

    max h / min h <= 2,
    min_(u,v) (P^2)_(u,v) >= p_* := (1/4) 10^(-(m-1)),          (1)
    shifted row-l1 norm of each free m-digit Parry mask
       <= D_m := 20 m^4.                                      (2)

To obtain (1) directly from the recorded estimate
(K^2)_(u,v) >= (1/2)10^(-v), where K=D^m/B_0, use
P^2=(B_0/lambda^m)^2 H^(-1)K^2H, B_0/lambda^m>=1, and
h_v/h_u>=1/2. Because P is stochastic, for every r>=2,

    (P^r)_(u,v) >= p_* .                                      (3)

Indeed P^r=P^(r-2) P^2 and each entry is a convex combination of entries of P^2.

We also retain the auxiliary-measure lemma used in the earlier note: there are probability measures mu supported in BA(kappa_mu), with dimensions delta tending to one, delta-Frostman complete-cylinder partitions, and

    |widehat(mu restricted to J)(xi)|
       <= C mu(J) (1+|J||xi|)^(-eta),                          (4)

uniformly over complete cylinders J, for every eta<e(delta), where

    e(delta)=delta(2delta-1)/((2delta+1)(3-delta)) -> 1/6.

This precise local estimate is the cylinder adaptation proved in the earlier note; it is not silently attributed to the global Fourier theorem. The primary global theorem is Lequen–Sahlsten,
https://arxiv.org/html/2607.18010v1 .
The rational slicing argument below uses exactly (4), and inherits its `proof sketch` status.

Finally theta_m=log_10(D_m)/m<1/6 for every m>=49, as certified by the exact integer comparison (20*49^4)^6<10^49 and monotonicity.

## Independent bridges replace forward forced transitions

Choose an integer r>=2 and a macroblock length L=rm; put B=10^L. As in the final parameter order, take r large enough that d_L>0. Given any compatible assignment a, choose one compatible reference path omega. Fix the automaton states at all macroblock boundaries to those of omega.

A macroblock is dirty when at least one of its digit positions belongs to F. Freeze every dirty macroblock to the corresponding reference word. On every clean macroblock, independently choose a word uniformly from all length-L legal bridges between its two fixed boundary states.

Every pair of states has a legal length-L bridge by (3). Concatenation is admissible because adjacent bridges have matching states. Every prescribed digit is realized because its entire dirty macroblock equals omega. There is no conditioning on an infinite event and no state-dependent possibility of future extinction.

Only o(J) of the first J macroblocks are dirty: their number is at most f(LJ). This is uniform over the assigned values and the reference path.

### The bridge law and its two costs

The free Parry probability of any particular length-L bridge u->v is

    lambda^(-L) h_v/h_u.

It is constant over all such words. Thus conditioning on the endpoint v is exactly the uniform bridge law. Its denominator is (P^r)_(u,v)>=p_*. Consequently every complete clean-block word has probability at most

    C lambda^(-L),       C := 2/p_*.                          (5)

Let R_L(t) be the length-L Parry Fourier matrix. The scalar Fourier mask of a uniform u->v bridge is

    q_(u,v)(t) = (R_L(t))_(u,v) / (P^r)_(u,v).

The row-norm induction in the earlier note and (2) give

    sup_t sum_(ell=0)^(B-1) |q_(u,v)(t+ell/B)|
       <= p_*^(-1) D_m^r.                                   (6)

For an explicit induction, write R_L(t)=M(B_0^(r-1)t)...M(t),
where M is the free m-digit mask. In ell=u+a B_0^(r-1), summing
over a leaves the first r-1 matrix factors unchanged by periodicity;
the final factor contributes at most D_m to the shifted row-l1 sum.
Repeat r times, then bound the selected entry by its row norm and
divide by the endpoint probability, which is at least p_*.

This estimate sums the modulus after the entire bridge matrix entry is formed. It does not replace a state-dependent continuation by the all-ones vector. The independent-bridge construction makes the resulting block masks scalar.

A deterministic dirty block has shifted sum B. A fully uniform block has shifted sum at most 2+log B, by
|U_B(t)|<=min(1,(2B||t||)^(-1)) and a harmonic sum. Set

    A_L := max(p_*^(-1)D_m^r, 2+log B),
    beta_L := log_10(A_L)/L,
    d_L := d_w - log_10(C)/L.                               (7)

As r tends to infinity with w fixed,

    beta_L -> theta_m < 1/6,        d_L -> d_w.              (8)

The bridge endpoint restrictions therefore cost vanishing entropy per digit and vanishing extra Fourier exponent. This is the step absent from the guarded-packet construction.

### An explicit macroblock witness

At the smallest retained word length, m=49, the choice r=500 gives
L=24500 and D_m=115296020. The following is an exact integer inequality,
checked by the accompanying audit:

    (4 * 10^48 * 115296020^500)^6 < 10^24500.                (8a)

The quantity inside parentheses exceeds 2+3L, hence also 2+log B.
Thus beta_L<1/6. Its informational decimal value is
0.1665105803216467707..., but that approximation is not used in the test.
Also C=8*10^48<10^49, so d_L>d_w-1/500.

In fact r=500 gives beta_L<1/6 for every m>=49. The bound from the
first term in A_L is

    1/r + [log_10(20)+4log_10(m)+(log_10(4)-1)/r]/m.

It decreases with m>=49: after multiplying its derivative by m^2,
the sign is that of
4/log(10)-log_10(20)-4log_10(m)+(1-log_10(4))/r<0.
Here the crude inequalities log(10)>2, log_10(20)>1, m>=10, and
0<1-log_10(4)<1 suffice. The same term dominates 2+log B:
D_m^r>=rD_m>2+3rm, using D_m>=2 and r>=1.
Increasing r only decreases the extra endpoint cost. Therefore one may
choose r>=500 with 1/r<d_w-s in the final parameter order. No numerical
Perron eigenvalue or numerical Markov constant is needed.

## Uniform estimates for finite-horizon measures

Run the independent-block process for n macroblocks and append independent uniform decimal digits. Let nu_n=g_n dx. The finite density g_n is a step function. Constants in the following estimates depend on w,F,L and the displayed positive parameters, but not on n, the assignment, or the reference path.

### Cylinder masses

For every epsilon>0,

    nu_n(D_b) <= C_epsilon 10^(-N(d_L-epsilon))              (9)

for every depth-N decimal cell D_b.

For N<=nL, ignore at most one unfinished macroblock. Apply (5) to the complete clean macroblocks and the trivial probability-one bound to dirty blocks. This gives

    nu_n(D_b)
       <= lambda^L 10^(-N d_L) lambda^(L f(N+L)).

Since f(N+L)=o(N), this implies (9). For N>nL the independent uniform tail contributes 10^(-(N-nL)); because d_L-epsilon<1, (9) continues to hold.

### Conditional tails, including scales inside forced packets

Condition on any positive-mass prefix b at a boundary depth N in L*N_0, and let tau_(n,b) be its rescaled tail probability measure. Because macroblocks are independent and their boundary states were fixed in advance, this tail does not depend on the realized prefix. It may depend on the reference path, which is harmless because (6) is uniform in the endpoint states.

Fix beta_L<alpha<eta. For every epsilon>0,

    sum_(|k|<=T) |widehat(tau_(n,b))(k)|
       <= C_epsilon 10^(epsilon N)(1+T)^alpha,             (10)
    sum_k |widehat(tau_(n,b))(k)|(1+|k|)^(-eta)
       <= C_epsilon 10^(epsilon N).                      (11)

To prove (10), use scalar mask multiplication and group the highest base-B frequency digit at each step. On a grid of B^J frequencies, (6) and the dirty-block bound give at most

    A_L^J B^(number of dirty tail blocks through J)
       <= A_L^J B^f(N+LJ).

Given a>0, f(X)<=aX+C_a. Choose La<epsilon and beta_L+La<alpha. The displayed expression is then at most a constant times
10^(epsilon N)(B^J)^alpha. Round T up to a B-power and use conjugate symmetry. Uniform blocks after the horizon satisfy the same clean bound by the definition of A_L. Dyadic summation gives (11).

The depth factor 10^(epsilon N) explicitly absorbs a tail beginning inside, or just before, a long forced packet. It is never absorbed by changing kappa with depth.

## Complete-cylinder slicing

Use an auxiliary mu satisfying (4). On the circle set

    rho_(n,t) = g_n(t-x) mu.

For an interval I of length rho, choose a boundary depth N with
rho<=h=10^(-N)<B rho. Stop the auxiliary coding at scale h and take the complete cylinders J meeting I. Their total mu mass is O(h^delta), and each reflected t-J meets at most three decimal cells of depth N.

For each such cell D_b write p_b=nu_n(D_b), and periodically extend the nonnegative density G_(n,b) of its rescaled tail. On J, apart from finitely many endpoints,

    g_n(t-x) <= h^(-1) sum_b p_b G_(n,b)(10^N(t-x)).        (12)

Pair each summand with the entire J. Equations (4) and (11) imply

    integral_J G_(n,b)(10^N(t-x)) dmu(x)
       <= C_epsilon mu(J)10^(epsilon N).

The pairing is pointwise valid by Fejer approximation: G is a finite step function, the finitely many preimages of its discontinuities have zero mu mass, and the paired Fourier series is absolutely summable. No estimate for a sharp decimal restriction of mu is used.

Combining this with (9), (12), and the cylinder mass sum gives

    rho_(n,t)(I) <= C_epsilon |I|^(d_L+delta-1-2epsilon)    (13)

whenever the exponent is positive, uniformly in n and t.

At N=0, (10) and the global case of (4) give a uniform absolutely summable Fourier tail. Choose one integer Q so that the tail on |k|>=Q is less than 1/2. The average of
H_n(t)=integral g_n(t-x)dmu(x) on the fixed Q-point rational grid is then greater than 1/2. Some fixed j in {0,...,Q-1} satisfies H_n(j/Q)>=1/2 along an infinite subsequence.

The corresponding measures rho_(n,j/Q) have a nonzero weak limit with the Frostman bound (13). Its reflection x->j/Q-x modulo one is supported in K_a, where a is the original digit assignment: every finite forbidden-word and digit prescription is satisfied for all sufficiently late horizons, and nested closed cylinders pass to the limit. Radix endpoints are rational and hence absent from BA.

Rational reflection takes BA(kappa_mu) into BA(kappa_mu/Q^2), since an approximation to j/Q-x of denominator q becomes an approximation to x of denominator Qq. Therefore the reflected limit has one fixed positive constant

    kappa = kappa_mu/Q^2.                                  (14)

All constants that fixed Q were uniform over the assigned digits and reference path. The selected rational numerator can vary with the assignment; kappa does not.

## Parameter order and conclusion

Fix 0<s<d_w.

1. Choose r so large that beta_L<1/6 and d_L>s.
2. Choose an actual auxiliary dimension delta sufficiently close to one that
   e(delta)>beta_L and d_L+delta-1>s.
3. Choose beta_L<alpha<eta<e(delta), then epsilon>0 with
   d_L+delta-1-2epsilon>s.
4. Fix the auxiliary measure, the uniform Fourier-tail denominator Q, and kappa from (14).
5. For each compatible assignment choose its reference and perform the construction.

Equation (13) gives dimension strictly larger than s and proves (A). Taking s up to d_w proves the full-dimension BA-union statement. Conversely K_a is contained in pi_10(Sigma_w), so its dimension cannot exceed d_w.

## What this adds, and what remains

The statement now covers arbitrary compatible sparse assignments in every one-word avoidance SFT with forbidden length at least 49. No guard, marker, special packet ordering, or forward-emission property is required. The same argument applies more generally to any primitive decimal SFT with finite-block Parry row-norm growth exponent strictly below 1/6.

The two-digit obstruction in
[the September 6 certificate](../../../../workflows/experiments/p1_two_digit_certificate_20260906/README.md)
is respected: this argument does not lower that growth exponent. It leaves short forbidden words, arbitrary positive-entropy SFTs, and every pi-digit target unresolved.

The [finite bridge audit](../../../../workflows/experiments/sparse_bridge_parry_audit_20261016.py)
uses the Python standard library and writes no files. Run it with
`python workflows/experiments/sparse_bridge_parry_audit_20261016.py`.
The local run passed nine models, 56 exact integer bridge-count and rational
normalization checks, and 224 floating-point Fourier comparisons (maximum
error below 9.3e-15). It also checked all 273 concatenations in a three-block
example with a frozen middle block and nonzero boundary states; the independent
block Fourier factorization had maximum error below 1.4e-14. The exact
m=49,r=500 parameter witness (8a) and the entropy-loss comparison also pass.
These are
`experiment`, not proof of the infinite dimension or local-decay assertions.

An independent adversarial review checked the legal-bridge Fourier induction,
the reference boundary states, dirty-block density, all-scales cylinder and
conditional-tail estimates, rational slicing, and assignment-uniform kappa.
The review requested an explicit matrix-grid induction and disambiguation
of the rational numerator; both have been incorporated. The status remains
`proof sketch`.

