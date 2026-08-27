# Finite-cylinder horizon-bootstrap separator

Status: `proof sketch`

Date: 2026-08-27 UTC

## Statement under audit

Let `D=10015` and let `P_D` be the T173 decimal prefix, so

\[
 P_D10^{-D}<\pi<(P_D+1)10^{-D}.
\]

Define the Liouville decimal

\[
 \lambda=\sum_{j\ge1}10^{-j!},\qquad
 \xi=P_D10^{-D}+10^{-D}\lambda.
\]

Then `xi` is transcendental, lies in the same strict T173 cylinder as pi,
and has only digits zero and one after position `D`.  The audited Pro argument
claims the following simultaneous separation:

1. the finite root inequality survives,
   `Re Z^xi_(1000,334)(10000) > 47539/2500`;
2. the generic T172 algebra therefore produces a positive fixed-horizon
   Bellman descendant at every scale;
3. for every `k>D` and every `A<10^k` with `A == 334 (mod 1000)`, the target
   word is absent from the entire decimal expansion of `xi`, and the generic
   T156 contrapositive gives

   \[
   \Re Z^\xi_{10^k,A}(10^k)<-861/1000.
   \]

Thus the finite cylinder, one finite signed root input, and all orbit-generic
coefficient identities cannot force natural-horizon signed control, even for
the coherent descendant class.

## Why the root sign is stable

For the generic decimal orbit `x_n^eta={10^n eta}`, the primitive score obeys
the Lipschitz estimate

\[
 |Z^\xi_{q,A}(N)-Z^\eta_{q,A}(N)|
 \le {2\pi\over9}(10^N-1)|\xi-\eta|
       \sum_u u|p_{q,A}(u)|. \tag{1}
\]

At `q=1000`, positivity of the boundary coefficients and the total positive
mass identity give the coarse bound

\[
 \sum_u u|p_{1000,334}(u)|<5000. \tag{2}
\]

Since `|xi-pi|<10^-10015` and `N=10000`, (1)--(2) make the score perturbation
less than `10^-11`, far below the directed root margin `>2.36*10^-5`.
This is the essential quantitative reason the countermodel can share the
actual-pi signed seed.

## Why natural horizons fail

Every left-descendant label remains congruent to `334 mod 1000`, so its padded
word ends in `334`.  A word of length `k>D` starting in the fractional
expansion must end after the certified prefix.  It therefore cannot occur in
`xi`, whose tail uses only digits zero and one.

The boundary kernel is strictly negative outside the target cylinder.  The
T147/T156 endpoint and scalar estimates convert absence through the natural
horizon into the strict score bound below `-861/1000` for pi.  Independent
audit found that this chain is not merely syntactically specialized:
T147 imports T146's actual-pi phase dichotomy, ultimately using
`nearestIntegerDistance (9*pi) > 13/50`.  Therefore a generic T156 cannot be
invoked without an explicit endpoint-separation premise.

For the concrete `xi` the gap appears repairable with the same constants:
the shared cylinder already gives `3.14 < xi < 3.15`, hence
`28.26 < 9*xi < 28.35`, so the nearest integer is 28 and the distance is
strictly greater than `13/50`.  This arithmetic lemma and the corresponding
parameterized T146--T156 chain are not yet machine-checked.

## Trust boundary and required audit

The construction, Liouville proof, decimal avoidance, and Lipschitz estimate
are elementary.  Before upgrading this result, Lean must expose generic orbit
versions of the T172/T176/T178 transport; parameterize T146--T156 under the
endpoint-separation premise just identified; prove that premise for `xi`; and
check the weighted coefficient estimate (2) against the literal T139
coefficients.  Canonical decimal-expansion uniqueness for the Liouville tail
must also be stated.  No claim about pi itself follows from the countermodel.

The separator is deliberately narrow: it does not exclude an actual-pi
horizon theorem.  It proves that such a theorem must import a premise false
for `xi`, hence genuinely fresh information about the uncertified actual pi
tail.  The most economical remaining quantities are

\[
 \Re\bigl(Z^\pi_{q,A}(q)-Z^\pi_{q,A}(10000)\bigr)
\]

or the corresponding prescribed T179 digit/suffix correlation on the fresh
block.  A tighter defect constant or another finite-cylinder identity cannot
cross this separator.

## Roth-optimal upgrade

The Liouville property of the displayed `lambda` is not essential. Let

```text
tau_10 = sum_(j>=1) t_j * 10^-j
```

be the base-ten Thue--Morse--Mahler number and define

```text
xi_TM = P_D * 10^-D + 10^-D * tau_10.
```

Its tail contains only zeroes and ones, so `xi_TM` lies in the same strict
T173 cylinder. Bugeaud's theorem gives `mu(tau_10)=2`; rational affine
invariance therefore gives `mu(xi_TM)=2`. Classical Mahler transcendence also
makes `xi_TM` transcendental. The exact exponent source is Y. Bugeaud,
*On the rational approximation to the Thue--Morse--Mahler numbers*, Annales
de l'Institut Fourier 61 (2011), DOI `10.5802/aif.2666`, already pinned and
audited in the T16 record.

The coherent-target orientation is important. If

```text
q_r = 1000 * 10^r,
A_(r+1) = A_r + d_r*q_r,
A_0 = 334,
```

then the padded target word is

```text
d_(r-1) ... d_1 d_0 334.
```

It ends in `334`; these are left extensions, not nested prefixes of one real
beginning with `334`. For every sufficiently large `r`, the terminal `334` of
any occurrence would lie beyond decimal position `D`, where `xi_TM` has only
zeroes and ones. Hence one `xi_TM` uniformly avoids every sufficiently deep
target on every coherent left ray. No prescribed-ray diagonalization is
needed.

The finite root score is not identical throughout the cylinder. It remains
positive only by the Lipschitz stability estimate (1)--(2) above. Likewise,
the checked T156 theorem is pi-specific. The natural-horizon conclusion for
`xi_TM` still requires the unformalized generic T146--T156 chain parameterized
by

```text
13/50 < nearestIntegerDistance (9*xi_TM).
```

This premise follows from the shared coarse cylinder
`3.14 < xi_TM < 3.15`, which puts `9*xi_TM` strictly between `28.26` and
`28.35`. Conditional on that parameterization, the same missed-cylinder
contrapositive gives

```text
Re Z^xi_TM_(q_r,A_r)(q_r) < -861/1000
```

eventually for every coherent ray.

This repaired statement remains a `proof sketch`, not `machine-checked`.
It strengthens the separator by showing that transcendence, non-Liouville
behavior, an effective finite irrationality measure, and even the optimal
irrationality exponent `mu=2` do not bootstrap the finite signed seed.
