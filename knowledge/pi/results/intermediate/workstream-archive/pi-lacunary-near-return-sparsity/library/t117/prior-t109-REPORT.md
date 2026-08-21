# T109: quantitative robustness transfer scout

Search date: 2026-08-10 UTC.

Claim labels: exact source statements below are `literature-checked` against the
seven delivered primary PDFs and locators in `SOURCE_PINS.md`. Every new
transport calculation and comparison is a `proof sketch`. The verifier checks
transcription, arithmetic, caps, and package integrity; it is not evidence for a
universal mathematical claim.

This report proves no statement about the decimal orbit of pi, canonical C1,
or C2. All three fingerprints are related-model mechanisms. Every bridge to pi
is an additional unproved premise.

```text
PRIMARY_SOURCE_COUNT: 9
PRIMARY_SOURCE_CAP: 12
SEARCHED_DOMAIN_COUNT: 3
RETAINED_FINGERPRINT_COUNT: 3
RETAINED_FINGERPRINT_CAP: 4
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

## 1. Immutable statement and normalized scope

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, it defines the ordered, diagonal-inclusive count

```text
Q_pi(n,N) = #{(i,j): 0<=i,j<N and
                       ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

The open canonical quantifiers are

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N) <= N^2.
```

`N` may depend on `A,n`; the cutoff is strict; pairs are ordered; all `N`
diagonal pairs remain. A theorem for a model process, invariant measure,
pseudo-orbit, coupling, or almost-everywhere point is an A13/A14 sibling only.

Normalized ambiguities for this item:

1. A stationary-process coupling does not couple deterministic finite prefixes
   of the named point pi.
2. Stability of invariant densities does not imply quantitative genericity of
   pi for that density.
3. Shadowing produces some true orbit, not necessarily the orbit starting at pi.
4. Transport closeness does not preserve hard decimal cylinder labels without
   boundary control.
5. T14 and T107 require one increasing prefix family across every triangular
   row, not separately selected good prefixes.
6. A fixed positive perturbation scale cannot control cylinder depths tending
   to infinity.

## 2. Bounded source audit

`SEARCH_LOG.md` enumerates all nine primary records opened: exactly three in
each required lane. Seven full PDFs were retrieved and pinned. S2 and S3 are
explicit retrieval blockers; no theorem is inferred from their abstracts. The
search stopped at nine, below the cap of twelve. Exactly three fingerprints are
retained; no candidate was added to fill the cap.

## 3. Mandatory exclusions and non-duplication

| Excluded mechanism | Exact comparison | Result |
|---|---|---|
| T104 ambient Fourier decay/nonlinear maps | T104 F3 uses total nonlinearity and twisted transfer operators; F4 uses ambient self-conformal Fourier decay and fails at named-point/adaptive uniformity | F3/F4 are excluded. S9 is screened as an F4 duplicate. F3 is not repackaged as robustness. |
| T105 additive energy | T105 studies additive/multiplicative energy, BSG subsets, and modular geometric-progression sums for `D_N` | No retained card uses additive quadruples, BSG, sum-product, modular order, or an unlocated subset. |
| Stoneham families | rational skeletons, prime-power residues, exact order, and stable coset multiplicity | No retained card uses constructed constants or modular repetition. |
| paperfolding | automatic/valuation recursion and finite-state symbolic collision profiles | No retained card uses paperfolding or automatic decimation. |
| Toeplitz towers | T103's periodic-hole tower, named Toeplitz point, and persistent hole density | No retained card uses periodic holes, tower heights, or Toeplitz returns. |
| universal charging | T100's machine-checked exact-word period charging | No retained card charges short exact-word collisions to remote repeats. |

The exact comparison pins are in `SOURCE_PINS.md`. The retained mechanisms are:

```text
F1: uniformly ergodic Markov-kernel perturbation -> coherent block-law TV bound
F2: ball-expanding pseudo-orbit shadowing -> pointwise orbit coupling
F3: Wasserstein transport -> finite-frequency Fourier-window stability
```

F1 is symbolic law transport, not symbolic recurrence. F2 is deterministic
shadowing, not nonlinear Fourier decay. F3 creates no Fourier decay; it only
transports an already available finite-window estimate.

## 4. Common collision-energy perturbation lemma

For a probability vector `p=(p_w)` on a finite alphabet, set

```text
C(p) = sum_w p_w^2.
```

If `dTV(p,q)=Delta`, couple `X~p` and `Y~q` with
`Pr[X!=Y]=Delta`, and take two independent copies of this coupling. The events
`X1=X2` and `Y1=Y2` can differ only if one coupling mismatches. Therefore

```text
|C(p)-C(q)| <= 2*Delta.                                  (4.1)
```

This is a `proof sketch` elementary inequality. Applied to empirical depth-ell
decimal word distributions, `C(p)=E_ell/P^2`, where `E_ell` is the ordered,
diagonal-inclusive collision energy at `P` starts.

Suppose a model distribution `q` has a strict one-step decrement

```text
C_(ell+1)(q) <= rho0*C_ell(q),                            (4.2)
```

and model/target block-law errors satisfy

```text
dTV(p_ell,q_ell) <= Delta_ell,
dTV(p_(ell+1),q_(ell+1)) <= Delta_(ell+1).
```

Then (4.1) gives

```text
C_(ell+1)(p)
 <= rho0*C_ell(p) + 2*(Delta_(ell+1)+rho0*Delta_ell).     (4.3)
```

Every distribution on `10^ell` labels has `C_ell(p)>=10^(-ell)`. Thus for
`rho0<rho`, the explicit sufficient T14 transfer test is

```text
2*(Delta_(ell+1)+rho0*Delta_ell)
  <= (rho-rho0)*10^(-ell).                                (T14-TV)
```

Under `(T14-TV)`, `C_(ell+1)(p)<=rho*C_ell(p)`. To invoke T14's machine-checked
reverse local bridge, choose fixed

```text
0 < eta <= 1/10,
1/10 < rho < (1-9*eta)^2.                                (4.4)
```

Locator: T14 `normalized_decrement_implies_quantitativeSplittingLevel`, lines
292-306, and the counted-level bridge at lines 310-327. Neither theorem asserts
the decrement for pi.

## 5. F1: uniformly ergodic Markov-kernel coupling

`FINGERPRINT_CARD: F1`

### Source theorem

S1 defines the total-variation norm of a signed measure as its full variation;
for the zero-mass differences of probabilities used below, this is twice
probabilists' total variation. See (2.1), printed p. 1004. It assumes a kernel
`P` with unique invariant law `pi_P` and

```text
||delta_x P^n - pi_P|| <= C*rho^n
for all x and n>=0, with C<infinity and 0<rho<1.           (5.1)
```

For a perturbed kernel `P_tilde`, put `E=P_tilde-P` and

```text
n_hat = ceil(log_rho(C^(-1))),
K = n_hat + C*rho^(n_hat)/(1-rho).
```

Corollary 3.1, equations (3.7)-(3.8), printed p. 1006, gives

```text
sup_n ||p_tilde_n-p_n|| <= ||p_tilde_0-p_0|| + K*||E||,
||pi_tilde-pi_P|| <= K*||E||                              (5.2)
```

when the perturbed invariant law exists. Theorem 3.1 and (3.1)-(3.6), printed
pp. 1005-1006, provide the finite-time bound behind (5.2).

### Explicit perturbation inequality

Let

```text
epsilon = sup_x dTV(P(x,.),P_tilde(x,.)).
```

Equation (5.2) gives invariant-law probabilistic TV at most `K*epsilon`.
Stepwise maximal coupling and a union bound then give the derived stationary
length-ell block-law estimate

```text
dTV(Law_P(X_0,...,X_(ell-1)),
    Law_Ptilde(Y_0,...,Y_(ell-1)))
 <= (K+ell-1)*epsilon.                                    (F1-TV)
```

If a pi empirical block law has additional error `sigma_(ell,k)` from the
perturbed model on prefix `P=N(k)`, define

```text
Delta_(ell,k) = sigma_(ell,k)+(K+ell-1)*epsilon_k.         (5.3)
```

Substituting (5.3) in `(T14-TV)` is the explicit F1 inequality aimed at T14.

### Additional pi-specific premise

One would need fixed parameters

```text
0<eta<=1/10, 0<=rho0<rho, 1/10<rho<(1-9*eta)^2,
d>0, B>=0, and integers m0,k0,
```

one strictly increasing positive `N(k)`, a probability measure `nu`, and
finite-alphabet kernels `P_tilde_k`.
The empirical pi measures along `N(k)` must converge weakly to `nu`. For every
`k>=k0` and `m0<=m<=k`, define `G_(m,k)` to contain exactly the levels
`0<=ell<m` at which the model decrement (4.2) and `(T14-TV)` both hold, where
the errors are (5.3). The additional quantitative premise is

```text
dTV(empirical_pi_block_law(ell,N(k)),
    stationary_Ptilde_k_block_law(ell)) <= sigma_(ell,k),
sup_x dTV(P(x,.),P_tilde_k(x,.)) <= epsilon_k,
and d*m-B <= #G_(m,k) for every k>=k0 and m0<=m<=k.       (PI-F1)
```

S1 supplies no decimal coding, no common prefix family, and no named-point
coupling for pi. `(PI-F1)` is not asserted.

### Cheap kill test

Set `sigma=0` to give the mechanism every advantage. At level `ell`, the test
requires

```text
epsilon_k <= (rho-rho0)*10^(-ell) /
  (2*((K+ell)+rho0*(K+ell-1))).                           (KILL-F1)
```

At `ell=k-1` this is exponentially small in `k`. Any proposed fixed positive
kernel error or polynomially decaying kernel error fails before any pi
computation. No conclusion about d-bar distance is drawn: S2-S3 were not
retrieved, and no comparison from d-bar to the displayed kernel error is used.
F1 is a clean robustness model, but it does not reduce the missing fixed-pi
input.

## 6. F2: deterministic shadowing for expanding maps

`FINGERPRINT_CARD: F2`

### Source theorem

S6 Definition 2.4, printed p. 3, calls `f` ball expanding on `M` when constants
`mu>1`, `nu>0` satisfy

```text
B_(mu*epsilon)(f(x)) subset f(B_epsilon(x))
for x in M and epsilon<nu.                                (6.1)
```

Theorem 4.3 and equations (4.1)-(4.2), printed pp. 10-11, state

```text
epsilon0=min(epsilon,nu), delta=(mu-1)*epsilon0            (6.2)
```

and conclude that every finite `delta`-pseudo-orbit in `M` is
`epsilon0`-shadowed by a true orbit, with an exact hit at the terminal point.
Two source-level cautions are material. Definition 2.4 assumes radii strictly
below `nu`, whereas the printed theorem permits `epsilon0=nu`; this report uses
only `epsilon<nu`. Also, the displayed inclusion chain on printed p. 11 reverses
the image inclusion implied by `J_i subset J_(i-1)`. The conclusion is recovered
by the elementary backward-lifting induction supplied by (4.2), but that repair
is a `proof sketch`, not a verbatim step of the printed proof.

For the circle map `T(x)=10x mod 1`, a direct local covering calculation gives
ball expansion with `mu=10` and `nu=1/20`. Thus the stated theorem, with the
proof-sketch repair just disclosed and this elementary specialization, gives
the explicit residual-to-shadowing budget: for every chosen
`0<epsilon<1/20`, set `delta=9*epsilon`; then

```text
max_j d(T(z_j),z_(j+1)) < delta
  implies d(T^j(y),z_j) < epsilon=delta/9.                (F2-SHADOW)
```

for some point `y`, at the finite times in the pseudo-orbit.

### Explicit perturbation inequality

Suppose two length-`P` point sequences `x_j,z_j` satisfy
`d_circle(x_j,z_j)<epsilon`. Let

```text
B_(ell,P)(x,epsilon)
 = #{j<P: x_j is within epsilon of a boundary a/10^ell}.
```

A depth-ell label can change only at one of these starts, so

```text
dTV(empirical_label_law_ell(x),empirical_label_law_ell(z))
 <= B_(ell,P)(x,epsilon)/P.                               (F2-TV)
```

The F2 inequality aimed at T14 is `(T14-TV)` with

```text
Delta_ell = B_(ell,P)(x,epsilon)/P.                       (6.3)
```

Equivalently, a model decrement (4.2) transfers whenever

```text
2*(B_(ell+1,P)+rho0*B_(ell,P))
 <= (rho-rho0)*P*10^(-ell).                               (F2-T14)
```

### Additional pi-specific premise

Theorem 4.3 produces some shadowing point `y`. Transfer to T14 requires fixed

```text
0<eta<=1/10, 0<=rho0<rho, 1/10<rho<(1-9*eta)^2,
d>0, B>=0, and integers m0,k0,
```

one strictly increasing positive `N(k)`, a weak limit `nu` of the empirical pi
measures along `N(k)`, and structured pseudo-orbits `z^(k)`.
For every `k>=k0`, `m0<=m<=k`, let `G_(m,k)` contain exactly the levels
`0<=ell<m` for which the model has (4.2) and `(F2-T14)` holds. One must prove
either that the source's shadowing point is pi, or directly

```text
d_circle(T^j(pi),z_j^(k)) < epsilon_k for every j<N(k),
and d*m-B <= #G_(m,k) for every k>=k0 and m0<=m<=k.       (PI-F2)
```

No inspected source identifies the shadowing point with pi or gives this
finite-prefix coupling. `(PI-F2)` is not asserted.

### Cheap kill test

For a proposed prefix and level, count only visits within `epsilon` of the
`10^ell` and `10^(ell+1)` grids and evaluate

```text
2*(B_(ell+1,P)+rho0*B_(ell,P))
  > (rho-rho0)*P*10^(-ell).                               (KILL-F2)
```

If this strict inequality holds, the displayed shadowing-to-T14 transfer is
rejected at that row. This `O(P)` boundary count is decisive for F2's stated
inequality; it does not claim that every other coupling argument fails. The
scalar `10^ell*epsilon` is only a cheaper warning: if it is not small, boundary
stability cannot be inferred without running `(KILL-F2)`. Even when the
boundary test passes, `(PI-F2)` still needs the named shadowing point.

## 7. F3: Wasserstein transport of a finite Fourier window

`FINGERPRINT_CARD: F3`

### Source theorems

S7 Theorem 7 and equation (24), printed pp. 10-11, prove for the paper's grid
measures and Fourier convention

```text
|mu_hat(k)-nu_hat(k)| <= |k|*W1(mu,nu).                   (7.1)
```

Theorem 8 and equation (26), printed pp. 11-12, give the reverse finite-grid
metric comparison. Only the forward Lipschitz estimate is used here. With the
circle convention `exp(2*pi*i*h*x)`, the same coupling proof gives

```text
|mu_hat(h)-nu_hat(h)| <= 2*pi*|h|*W1(mu,nu).              (F3-FOURIER)
```

S8 considers two-map equicontractive IFSs

```text
S1(x)=c*x+t1, S2(x)=c*x+t2,
0<c<=1/2, 0<=t1<=1-2c, t1+c<=t2<=1-c,
```

with Bernoulli weights `(p,1-p)` and `(p',1-p')`, under the source's standing
conditions `p,p' in (0,1)` and `p != p'`. Corollary 2.6, printed pp. 5-6,
computes exactly for Euclidean `W1` on the interval

```text
W1(mu_p,mu_p') = ((t2-t1)/(1-c))*|p-p'|.                 (7.2)
```

In the middle-`(1-2c)` case the interval value is exactly `|p-p'|`. Theorems
2.1 and 2.3, printed pp. 4-5, compute first and second moments for the
underlying self-similar couplings. After quotienting the interval to the
circle, the quotient map is 1-Lipschitz, so this interval value is only an
upper bound for circle-geodesic `W1`; equality is not asserted.

### Explicit T107 perturbation inequality

For T64's collected coefficient tensor, define the exact finite weighted norm

```text
Lambda(Q,H) = sum_((h,k)!=(0,0))
  ||C_(Q,H)(h,k)||*(|h|+|k|),
A(q) = Lambda(10*q,8000*q^3) + (1/2)*Lambda(q,40*q^3).    (7.3)
```

If `R_(q,P)(mu)` denotes the T64 row remainder with each finite spectrum
replaced by `P*mu_hat`, the product identity and `(F3-FOURIER)` give

```text
||R_(q,P)(mu)-R_(q,P)(nu)||
 <= 2*pi*P^2*W1(mu,nu)*A(q).                              (F3-ROW)
```

This uses only `|mu_hat|,|nu_hat|<=1`. T64's machine-checked theorem
`nonzeroCollectedFejerL1Norm_le`, lines 645-701, says

```text
sum ||C_(Q,H)|| <= 16*(2+log(H/Q+1))^2.
```

Since `|h|+|k|<=2H`, it yields the explicit coarse bound

```text
A(q) <= q^3 * [
  256000*(2+log(800*q^2+1))^2
  + 640*(2+log(40*q^2+1))^2].                            (7.4)
```

The successor and parent orders are pinned at T64 lines 1416-1418, and the row
combination at lines 1715-1720. If a model has half of T107's Fourier budget,

```text
||R_(q,P)(nu)|| <= P^2/(20*q),                            (7.5)
```

then the literal full Fourier budget follows from

```text
W1(mu,nu) <= 1/(40*pi*q*A(q)).                            (T107-W1)
```

The coarse sufficient rate from (7.4) is order
`q^(-4)*(log q)^(-2)`. This is finite-window stability, not ambient Fourier
decay.

### Additional pi-specific premise

The full premise cannot stop at a rowwise Fourier bound. It must retain T107's
common prefix, weak limit, boundary load, and affine triangular average. An
explicit sufficient premise is the following. There exist fixed

```text
d>0, B>=0, m0>=1, k0, a strictly increasing N with N(k)>0,
and a probability measure nu such that
(1/N(k))*sum_(j<N(k)) delta_(10^j*pi) -> nu weakly.        (7.6)
```

For every `k>=k0`, `m0<=m<=k`, and `ell` with `1<=ell<m`, put
`P=N(k)`, `q=10^ell`. Choose a model measure `nu_(ell,k)` and define

```text
b_(ell,k) = (40*q/P) * [
  activeBoundaryCount_successor(ell,P)
  + (1/2)*activeBoundaryCount_parent(ell,P)],

f_(ell,k) = (10*q/P^2)*||R_(q,P)(nu_(ell,k))||,

w_(ell,k) = 20*pi*q*A(q) *
  W1((1/P)*sum_(j<P) delta_(10^j*pi),nu_(ell,k)).          (7.7)
```

The boundary counts in (7.7) use exactly T107's widths `1/(400*q^2)` at
depth `ell+1` and `1/(4*q^2)` at depth `ell`. Require, for every triangle
entry,

```text
sum_(1<=ell<m) max(b_(ell,k),f_(ell,k)+w_(ell,k))
  <= #{ell:1<=ell<m} - (d*m-B).                           (PI-F3)
```

By `(F3-ROW)`, the actual normalized Fourier defect is at most `f+w`; its
normalized boundary defect is exactly `b`. Thus `(PI-F3)` is the literal T107
averaged-defect premise on the same `N(k)`, with every fixed parameter and weak
limit visible. The half-budget test `(T107-W1)` is a convenient sufficient test
for one Fourier row, not a substitute for this affine sum. T107 locators are
lines 153-173 for the exact premise and lines 259-297 for the bridge.

T107's boundary budget is not a consequence of Wasserstein closeness. S7-S8
do not supply `(PI-F3)`, the common prefix family, its weak limit, or any
statement about pi.

### Cheap kill test

First compute the exact finite `A(q)` and test the actual circle-geodesic
Wasserstein gap against `(T107-W1)`. Replacing `A(q)` by its coarse upper bound
can certify a sufficient pass condition, but cannot certify rejection. With
the exact `A(q)`, the decisive rejection is

```text
W1_circle(mu,nu) > 1/(40*pi*q*A(q)).                      (KILL-F3)
```

In the S8 middle-Cantor calibration, (7.2) and the 1-Lipschitz quotient show
that `|p-p'| <= 1/(40*pi*q*A(q))` is a sufficient pass condition, not an exact
rejection test. Every fixed positive *actual circle-Wasserstein gap* fails as
`ell` grows. S9 Theorem 1.4, printed p. 2, fixes `m,C1,C2,epsilon,s`, assumes
bounded contraction ratios, nontrivial translations, and `min q_j>=epsilon`,
then produces an exceptional set of Hausdorff dimension at most `s` and an
existential uniform exponent `alpha>0` outside it. It gives no numerical
exponent, no necessity statement, no named-parameter certificate, and no
`(PI-F3)`, so its use here is rejected as a T104-F4 duplicate before this test.

## 8. Cross-card negative map

| Card | Controlled quantity | Exact transfer threshold | First fatal fixed-pi gap | Cheap rejection |
|---|---|---|---|---|
| F1 | stationary finite-word law under a uniformly ergodic kernel perturbation | `(T14-TV)` with (5.3) | exponentially accurate coherent coupling of pi empirical block laws to the perturbed Markov model | `(KILL-F1)` |
| F2 | pointwise finite pseudo-orbit shadowing | `(F2-T14)` | the shadowing point is not identified with pi; boundary visits are uncontrolled | `(KILL-F2)` |
| F3 | a prescribed finite Fourier tensor under Wasserstein transport | `(T107-W1)` and the full affine premise `(PI-F3)` | `q^-4` transport, boundary control, weak convergence, and affine average on one common pi prefix family | `(KILL-F3)` |

The three mechanisms are quantitatively explicit and semantically distinct,
but all demand scale-dependent coupling information at least as strong as the
unavailable named-point input. None supplies a survivor that can be developed
without merely renaming the missing pi estimate.

## 9. Scope firewall

1. No delivered source states a theorem about pi.
2. No source or derived inequality establishes the canonical near-return bound.
3. No source or derived inequality establishes C1 or C2.
4. The T14 and T107 conclusions are conditional on `(PI-F1)`, `(PI-F2)`, or
   `(PI-F3)`, none of which is asserted.
5. Finite or model measures are not empirical limit measures for pi.
6. The negative tests reject these displayed transfers, not every future
   robustness mechanism.

## 10. Replay

From a directory containing only the delivered artifacts, run

```text
python3 verify_t109.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and PDF hashes, cap and domain markers,
mandatory-exclusion strings, candidate/premise/kill markers, one terminal
decision, and zero successors. Its finite arithmetic replay checks the
coefficients in (7.4) and sample instances of (4.1)-(4.3). It does not validate
source locators, theorem transcription, or the universal derivations; those
remain inspectable prose obligations. These are integrity and finite arithmetic
checks, not proof of a universal statement.

TERMINAL_VERDICT: close

The sole terminal classification is **close**. The bounded map found three
useful robustness models, but F1 and F2 require exponentially accurate symbolic
or pointwise coupling to the named pi orbit, while F3 requires roughly
`q^-4*(log q)^(-2)` Wasserstein accuracy plus independent T107 boundary control.
No inspected source supplies those premises. There is no bounded successor
(`SUCCESSOR_COUNT: 0`). This closes only the audited robustness-transfer
fingerprint and makes no claim of progress on pi, C1, or C2.
