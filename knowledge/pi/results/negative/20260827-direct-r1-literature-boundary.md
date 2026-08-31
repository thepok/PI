# Direct R1 literature boundary

Claim status: `literature-checked` for the cited source hypotheses and the
bounded PaperSearch comparison below.  One pointwise theorem applies to the
actual π orbit, but it supplies no target location or signed sum.

Search date: 2026-08-27 UTC.  The local PaperSearch database at
`/home/Marcel/dev/AllMath/paper-search.sqlite3` contained `776632` records,
including `187052` with extracted full text.  The
search targeted the live natural-diagonal fresh contribution

```text
D_d = q*(Delta_0+Xi_d)-21/10
```

and the same-digit R2 condition `D_d>0` and `G_d+D_d>0`.  It looked for
pointwise lacunary theorems at explicit constants, Mahler or special-value
mechanisms with ordered real sign, and results stated specifically for pi.

## Pointwise actual-π input and its sharp boundary

A focused rescan on 2026-08-29 found Dubickas,
[There are infinitely many limit points of the fractional parts of
powers](https://arxiv.org/abs/math/0512314).  Its theorem states that for
algebraic `alpha>1` and real `xi>0`, the sequence `{xi*alpha^n}` has finitely
many limit points exactly when `alpha` is a PV number and
`xi in Q(alpha)`.  Taking `alpha=10` and `xi=pi` proves the genuine pointwise
actual-π statement

```text
the decimal orbit {fract(10^n*pi): n>=1} has infinitely many limit points.
```

Here `10` is a PV number, while the transcendence of π gives
`pi notin Q(10)=Q`.  This is deterministic Archimedean information about the
distinguished orbit, not an almost-everywhere conclusion.

The source also shows sharply why it does not imply a target hit.  For every
integer base `b>=2`, the transcendental Liouville number
`xi=sum_(k>=0)b^(-k!)` has limit set exactly

```text
{0,b^-1,b^-2,...}.
```

Thus even a transcendental seed with infinitely many limit points can omit
essentially every prescribed decimal cylinder.  The theorem provides no
location, density, return rate, target rotation, or signed partial-sum bound,
so it cannot imply either the flexible `-122091/200000` barrier or T189 FMR.
Reopen this input only with a π-specific strengthening that forces the limit
set quantitatively into literal target cylinders or directly signs the
target-weighted return sum.

An independent PaperSearch audit on 2026-08-29 closes the tempting repair by
an irrationality-exponent hypothesis.  Wen--Wu,
[Hankel determinants of the Cantor
sequence](https://arxiv.org/abs/1407.3578), define

```text
c_0=1,  c_(3n)=c_(3n+2)=c_n,  c_(3n+1)=0,
xi_(c,b)=sum_(k>=0) c_k*b^(-k),
```

and prove for every integer `b>=2` that the transcendental Cantor number
`xi_(c,b)` has the optimal irrationality exponent

```text
mu(xi_(c,b))=2.                                      (WW)
```

For `b=10`, shifting the base-ten expansion gives the elementary exact bound

```text
forall n>=0: fract(10^n*xi_(c,10))
  = sum_(j>=1) c_(n+j)*10^(-j) in [0,1/9].          (C)
```

Thus transcendence, infinitely many limit points, and even `mu=2` coexist
with an orbit that permanently omits every cylinder outside `[0,1/9]`.  If
`phi` is any nonnegative continuous function supported in one such omitted
cylinder with positive integral, (C) also gives the deterministic signed
separator

```text
sum_(n<N) (phi(fract(10^n*xi_(c,10)))-integral phi)
  = -N*integral phi.
```

This is stronger than the preceding Liouville separator for the proposed
repair: no hypothesis depending only on a finite irrationality exponent can
force target-uniform signed recurrence, even at the smallest possible value
`mu=2`.  Allouche--Glen,
[Distribution modulo 1 and the lexicographic
world](https://arxiv.org/abs/0907.3560), reproduce the sharp
Bugeaud--Dubickas theorem that an irrational base-`b` orbit cannot fit in an
interval shorter than `1/b`, while exact `1/b` confinement occurs precisely
for adjacent-digit Sturmian expansions and is transcendental.  Thin orbit
closures are therefore compatible with strong Diophantine behavior at the
optimal geometric confinement scale.

### Phase-preserving two-seed strengthening

Bugeaud--Han--Wen--Yao,
[Hankel determinants, Padé approximations, and irrationality
exponents](https://arxiv.org/abs/1503.02797), cover the
Kmošek--Shallit/Mahler number

```text
kappa = sum_(m>=0) 10^(-2^m),
```

which is transcendental with `mu(kappa)=2` (`literature-checked`).  Direct
tail analysis gives

```text
omega(kappa) = {0} union {10^-j : j>=1}.            (proof sketch)
```

Define `eta_0=kappa`, `eta_2=2/9+kappa` and

```text
xi_0 = 3.14 + 10^-2*eta_0,
xi_2 = 3.14 + 10^-2*eta_2.
```

Their tails use the disjoint alphabets `{0,1}` and `{2,3}`.  Accounting for
the unique shared prefix digit `4` shows that their length-`k` languages are
disjoint for every `k>=3`.  Thus for every literal `(k,A)` one fixed member
avoids that target forever.  Both have `mu=2`, infinite sparse omega-limit
sets, linear factor complexity and logarithmically many digit changes.

Both also lie strictly between `3.14` and `3.15`, so

```text
nearestIntegerDistance(9*xi_r) > 13/50.
```

An independent proof audit of T146--T148 found this to be the only
seed-specific input to the `7/500` endpoint saving: the torus dichotomy uses
only `theta_2=10*theta_1-9*xi`, while the Abel, layer-mass and terminal bounds
are seed-independent.  Exposing the orbit argument in T139 therefore gives

```text
target (k,A) avoided by xi_r
  -> forall N>=10^k:
       Re PBFS_(xi_r)(10^k,A,N) < -122091/200000.   (proof sketch)
```

This audited parametric replay is not a compiled declaration.  It shows that
finite `mu`, infinite omega, the known complexity/change consequences, the
actual prefix `3.14`, and even the exact local phase input behind T147 can all
coexist with the strict wrong sign at every admissible horizon.  A
target-dependent bridge of `k-1` digits followed by one of the two tails also
preserves any target-free finite π prefix while avoiding that target forever.

The separator must not be overstated as a literal substitution into the
repository's flexible primitive-sum threshold.  The current T139 definition
of `primitiveBoundaryFourierSum` and the T148 consumer are specialized to
`piOrbit`; moreover, T148's final endpoint improvement uses the genuinely
actual-π T147 saving `7/500`.  For a target cell with `A/q>1/9`, Wen--Wu
confinement does feed the orbit-generic machine-checked T128 avoidance
consumer.  A straightforward but currently unformalized genericization of
the T139 compression would then give, for `N>=q`, only

```text
Re P_x(q,A,N) < -119291/200000,                     (proof sketch)
```

not the active π barrier `-122091/200000`.  The difference is exactly
`7/500`, the unavailable T147 endpoint saving.  Thus the example decisively
rules out `mu` as the missing target-location/sign source, but it does not
prove a theorem about the π-specialized primitive sum by type-changing its
orbit.
The stronger `xi_0,xi_2` construction above repairs exactly this missing
phase premise, but still only for its explicitly parameterized paper-level
PBFS.

Reopen the omega-limit/irrationality-exponent route only with a genuinely
pi-specific input that excludes proper decimal subshifts or directly locates
target-dependent returns.  No condition stated solely through `mu(pi)` can
provide the missing sign.

## Controlled finite-level Siegel products collapse to one lifted orbit

An independently audited `proof sketch` closes a narrower modular-unit route.
Let `L=10^k` and form a finite product of Siegel functions with characteristics
`(p_j/L,t_j/L)` and total exponent mass `M`. Writing

```text
rho = (1/2) * sum_j m_j*B_2(p_j/L),
nu  = 12*L^2*rho in Z,
```

the product factors exactly as

```text
U(tau) = C*q^rho*Psi(q^(1/L)),
|Log Psi(z)| <= 3*M*|z|/(1-|z|)^2.
```

On `tau_s=10^s*(alpha+i*eta)`, `s>=2k+2`, put

```text
w_s = exp(2*pi*i*10^(s-2k-2)*alpha/3),
r_s = exp(-2*pi*eta*10^(s-k)).
```

Then exactly

```text
U(tau_s)
 = C*exp(-2*pi*rho*eta*10^s)
     *w_s^(25*nu)*Psi(r_s*w_s^(3*10^(k+2))).
```

Thus a controlled high-cusp finite Siegel package with stable Lipschitz phase
decoding supplies only a target-dependent integer power of the single lifted
orbit `{10^m*alpha/3}`, plus an exponentially small tail. The target
characteristic `p_j` also changes `nu`; it is not confined to `C` and `Psi`,
but it still creates no independent phase. Streng's generator theorem covers
the rational modular-unit group modulo constants through constrained products
of the untwisted generators; arbitrary target-twisted products need not
themselves be modular units.

This is deliberately not a general modular or automorphic no-go. Escape is
possible through a level already around `10^s/log q`, growing exponent mass,
non-Lipschitz or ill-conditioned decoding, varying cusp height, or a genuinely
dynamic CM coupling. Reopening the controlled class requires an independent
signed theorem for `{10^m*pi/3}`; modularity alone does not sign that orbit.

## Closest source families

1. Aistleitner, [Metric number theory, lacunary series and systems of dilated
   functions](https://arxiv.org/abs/1306.3315), records discrepancy and LIL
   theorems for Hadamard-gap sequences.  Their strong fluctuation conclusions
   are explicitly for almost every `x`.  They do not select `x=pi`, handle the
   target-dependent growing T179 kernel, or align a fresh digit with `G_d`.

2. Moshchevitin, [A version of the proof for Peres--Schlag's theorem on
   lacunary sequences](https://arxiv.org/abs/0708.2087), Theorem 1, constructs
   an `alpha` satisfying a uniform lacunary avoidance bound.  Specializing to
   `d=1`, `M=8`, and `t_j=10^j` gives

   ```text
   exists alpha, forall j>=1:
     ||10^j*alpha|| >= 1/(2^14*log 8).
   ```

   The quantifier constructs a favorable number; it supplies no information
   for the prescribed number `alpha=pi` and only avoids integers rather than
   signing R1.

3. Costin--Huang, [Behavior of lacunary series at the natural
   boundary](https://arxiv.org/abs/0810.3027), gives Abel-regularized
   magnitude and boundary expansions, with exact finite decompositions at
   rational/root-of-unity angles.  It does not give a sign for a finite block
   at `exp(2*pi*i*pi)` or for the complete target-dependent primitive score.

4. Zorin, [Algebraic independence and normality of the values of Mahler's
   functions](https://arxiv.org/abs/1309.0105), proves quantitative
   nonvanishing for algebraic-coefficient Mahler systems evaluated along
   contracting interior orbits.  The evaluation point may itself be
   transcendental; algebraicity of the point is not the obstruction here.
   For `p(z)=z^10` and a single Mahler function, however, the theorem's stated
   dimension cutoff is empty, and the actual decimal pi phase lies on the
   noncontracting unit circle.  It supplies neither a boundary value nor an
   order on a real part.

   The complete literal nonzero-sector packet sharpens only the continuation
   boundary (`proof sketch`; Randé's theorem in the
   [Bell--Coons--Rowland proof](https://arxiv.org/abs/1210.2070)
   `literature-checked`; independently audited).  For its finite packet
   polynomial `P`, the completed carrier

   ```text
   F(z)=sum_(n>=0) P(z^(10^n))
   ```

   is nonrational and has the unit circle as a natural boundary.  Therefore
   one cannot order a finite boundary block by separately analytically
   continuing its two carrier endpoints.  The endpoint difference itself is
   the original finite polynomial and is entire; radial or simultaneous
   limits and direct arithmetic boundary identities remain open.  In the
   corresponding Abel--Mellin representation, the boundary limit has no
   uniform absolute majorant on the original positive inversion line because
   the lower-tail Gamma decay is exactly cancelled and the finite Dirichlet
   polynomial has positive mean square (`proof sketch`, independently
   audited).  This is not a general contour obstruction: shifting first to
   `Re(s)<-1/2` restores absolute integrability of the finite remainder.

5. Barral--Loiseau, [Large deviations for the local fluctuations of random
   walks and new insights into the "randomness" of
   Pi](https://arxiv.org/abs/1004.3713), proves large-deviation properties for
   almost every path of suitable stochastic systems.  Its statement that the
   base-`m` digits of pi satisfy property `(P)` is explicitly labeled a
   conjecture supported by numerical experiments.  Even that conjecture does
   not state the same-witness R2 alignment.

6. Lagarias, [On the Normality of Arithmetical
   Constants](https://arxiv.org/abs/math/0101055), Theorem 3.1a, gives an
   exact asymptotic bridge between ordinary radix and perturbed BBP remainder
   orbits. Its distribution conclusion depends on the explicitly unproved
   Hypothesis A. The proved bridge is only `o(1)` in torus distance and gives
   neither a one-sided local gauge bound, a `1/q` rate, nor decimal
   same-digit alignment for DC1. More precisely, if
   `E_q=sup_(m>=q+1)|epsilon_m|`, direct use of the two literal T179 residue
   classes gives

   ```text
   |P_1(pi)-P_1(shadow)| < 200*pi*q^2*E_q,
   |DC1_pi-DC1_hybrid| < 100*pi*sec(pi/10)*q^3*E_q.
   ```

   Thus even a constant-margin hybrid DC1 transfer needs `E_q=o(q^-3)` plus
   an independent positive signed carrier margin. A degree-gap-one rational
   perturbation has only `E_q=O(q^-1)`. The familiar pi BBP formula is also
   power-of-two based, not a literal decimal rational-function expansion.

7. Beukers--Tijdeman, [A one-sided power sum
   inequality](https://arxiv.org/abs/1107.5495), proves signed pointwise lower
   excursions for fixed conjugate unit-circle exponential polynomials after
   selecting an unrestricted exponent. This is the closest inspected
   deterministic one-sided theorem. DC1 changes both coefficients and
   inherited deficit with the node and needs the prescribed natural-scale
   block; the theorem has no effective hitting time, fixed-node selector, or
   coupling to actual pi.

   A proof-level specialization sharpens this mismatch. Every fixed literal
   T179 paired-sector Laurent polynomial satisfies the source hypotheses, so
   in every complex direction it has syndetic positive excursions under
   integer dilation `z -> z^m`; at natural scales the directional amplitude
   is `>1/(450q)`. But the theorem selects an unrestricted integer `m`. A
   syndetic set can avoid every `10^s`, and `m` changes the constant from pi
   to `m*pi`; even `m=10^s` shifts the fresh block without transporting the
   same node's inherited DC1 deficit. The right-size excursion therefore
   occurs at the wrong quantifier.

## Boundary

The inspected literature splits at the wrong quantifier:

- signed lacunary fluctuation theorems hold almost everywhere in `alpha`;
- pointwise avoidance theorems construct some favorable `alpha`;
- Mahler value estimates apply on contracting interior orbits (sometimes even
  at transcendental points), while natural-boundary theorems give no value or
  sign at the distinguished unit-circle phase;
- the direct pi stochastic statement is conjectural;
- the strongest one-sided power-sum result selects a free exponent for fixed
  coefficients, not the moving literal T179 polynomial at the required node.

None of these results proves R1 on an unbounded coherently reached actual-pi
path, and none couples the same digit to R2.  This is a dated bounded
literature boundary, not a proof that no relevant theorem exists outside the
searched corpus or can be developed later.
