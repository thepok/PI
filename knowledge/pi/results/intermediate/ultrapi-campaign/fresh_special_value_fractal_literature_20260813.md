# Fresh special-value, fractal, and lacunary-gap literature audit

Audit date: **2026-08-13 UTC**

Status: `literature-checked`

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The target is Marcel's immutable local question and has no external source
URL; none is invented here.  No formal or `ultrapi.md` file was changed by
this audit.

## Outcome

No primary theorem located in the bounded search through 2026-08-13 proves
that every finite decimal word occurs in \(\pi\), excludes \(\pi\) from every
one-word survivor, or proves density of \(\{10^n\pi\}\).  This is a bounded
search result, not an impossibility statement.  Canonical V1 remains a
`conjecture`.

There is, however, one material new alignment.  Peres--Yang,
[arXiv:2606.28860v1](https://arxiv.org/abs/2606.28860v1), Theorem 1.2 on
paper page 2, proves for every Hadamard-lacunary integer divisibility chain
\(a_n\mid a_{n+1}\) that, for Lebesgue-almost every \(x\),

\[
                  \frac{N G_N(x)}{\log N}\longrightarrow1,             \tag{1}
\]

where \(G_N(x)\) is the largest circular gap in
\(\{a_1x,\ldots,a_Nx\}\).  Taking \(a_n=10^n\) gives exactly the sharp
largest-gap scale for the decimal orbit, and it agrees strikingly with the
local BBP endpoint `experiment`

\[
                  G_e^\pm\asymp\frac{\log L_e}{L_e}.                    \tag{2}
\]

This is the closest theorem found to the current endpoint-gap route.  It does
**not** specialize to \(x=\pi\), and it also does not apply to the triangular
array \(x=B_{M_e^\pm}\), where the rational point and the starting exponent
both change with the row.  The paper's proof uses Lebesgue measure and, for
the sharp lower bound, independent mixed-radix digits.  Neither input is
known for the named point \(\pi\) or for the selected BBP numerators.

The most useful new research target is therefore not a new normality
criterion.  It is an endpoint-specific deterministic analogue of the
Peres--Yang no-hit estimates: prove that every interval of length
\(C\log L_e/L_e\) is hit by each sufficiently late exact BBP endpoint row.
Together with the already audited shadow and late-exponent premises, this is
the missing uniform-cover premise in the `machine-checked` T75 bridge and
would imply V1.  The proposed lemma is stated precisely in Section 6.

## 1. Normalized statement and quantifier hazards

Canonical V1 is

\[
 \forall m\ge1\ \forall a\in\{0,\ldots,10^m-1\}\ \exists n\ge0:\qquad
       \left\lfloor10^m\{10^n\pi\}\right\rfloor=a.                    \tag{3}
\]

Leading zeroes are retained.  This is equivalent to decimal disjunctivity,
not normality.  If a word \(w\) of length \(m\) is absent, every decimal tail
of \(\pi\) lies in its proper graph-directed survivor \(K_w\).  It also lies
in the coarser homogeneous base-\(10^m\) missing-digit set obtained by
forbidding \(w\) only at aligned block positions.  The reverse implication
does not hold.

The following distinctions are essential in applying the sources below.

- A theorem for almost every point of a measure does not include the named
  point \(\pi\) without a separate typicality theorem.
- Existence of normal points in a thin Cantor set does not identify \(\pi\)
  as one of them.
- A dimension drop can leave a nonempty, countable, or singleton
  intersection; it does not exclude a named point.
- Membership of \(x\) in a decimal survivor makes \(\{10^n x\}\) remain in
  the survivor.  It says nothing analogous about \(\{16^n x\}\).
- A rational lying in an infinite missing-digit set is much stronger than a
  rational BBP shadow having a long legal finite prefix.
- Peres--Yang fixes \(x\) and lets \(N\to\infty\).  The BBP endpoint
  experiment uses a different rational \(B_M\) in every row.
- A full two-parameter \(\times10,\times16\) orbit theorem cannot be
  restricted to the one-parameter decimal slice without an additional
  recurrence or transversality statement.

## 2. Delta from the existing local audits

The following local reports were read before the fresh search:

- [special_values_digit_complexity_literature.md](special_values_digit_complexity_literature.md),
  current SHA-256
  `b08859d7fa8e68402e26393a76dffb010b19a3dbb442053b6765e87f1b67ece9`;
- [subshift_log_algebraic_bridge.md](subshift_log_algebraic_bridge.md),
  current SHA-256
  `b4e4fb05397f75e1e4af7bbd6d4d32e80d489893fead9773de51a57a28aca896`;
- [three_primary_resonance_literature.md](three_primary_resonance_literature.md),
  current SHA-256
  `80569b4e0d4c00803c8b76156e30be6ed1ce5dfaf2a175c4a74eb176b3dd16f8`;
- [pi_centered_carry_density_literature_audit_20260813.md](pi_centered_carry_density_literature_audit_20260813.md),
  current SHA-256
  `61537ce66782bd89e96a7224d877acaf5f169b431beb2ca2ac0eaa11ea6fbd96`;
- the independent SFT/log audit, the G-function/SFT audit, the
  Furstenberg--BBP bridge, and the general 2025--2026 literature report.

Those reports already cover Fischler--Rivoal on E- and G-values,
Snodgrass on exponential periods, Adamczewski--Bugeaud and recent
Bugeaud--Kim complexity bounds, Shmerkin--Wu and related Furstenberg slice
theorems, Maynard and restricted-digit Fourier estimates, the
Chow--Varjú--Yu and Iyer restricted-denominator routes, and the 2025--2026
lacunary-covering papers previously pinned there.  They are not repackaged as
new findings here.

The genuine deltas are:

1. Peres--Yang's sharp maximal-gap theorem and its blockwise no-hit estimates;
2. Jiang--Li--Li--Wu's 2026 dimension-drop theorem for a homogeneous Cantor
   set intersected with a rational-slope affine copy;
3. new 2026 metric shrinking-target, sparse-Cantor normality, digit-mixing,
   G-function height, and rational missing-digit criteria, audited below for
   exact applicability.

## 3. Closest theorem: Peres--Yang maximal gaps

Let \((a_n)\) satisfy the Hadamard gap condition
\(a_{n+1}/a_n\ge q>1\), and let \(G_N(x)\) be the maximal empty circular gap
of \(\{a_nx:1\le n\le N\}\).

Peres--Yang, Theorem 1.1, paper pages 1--2, proves for Lebesgue-almost every
\(x\)

\[
 \frac12\le\liminf_{N\to\infty}\frac{NG_N(x)}{\log N}
 \le\limsup_{N\to\infty}\frac{NG_N(x)}{\log N}
 \le\frac{q+1}{q-1}.                                      \tag{4}
\]

Their Theorem 1.2, paper page 2, adds \(a_n\mid a_{n+1}\) for every \(n\)
and obtains the sharp limit (1).  In particular it applies to
\(a_n=10^n\), but only for almost every \(x\).

The upper-bound mechanism is especially relevant:

- Proposition 4.3, paper page 14, for every fixed
  \(\beta,\tau,\varepsilon>0\) and an interval \(J\) of length
  \(s=\tau\log N/N\), gives uniformly in \(J\)

  \[
  \lambda\{x:a_nx\notin J\ (1\le n\le N)\}
   \le N^{-\tau/(\beta+1+2(\Gamma+\varepsilon))+o(1)}+O(N^{-4});       \tag{5}
  \]

- Proposition 5.2, paper page 16, for fixed \(\beta,\tau>0\), improves this
  for the paper's \(R_N\)-regular intervals of length
  \(s=\tau\log N/N\) in a divisibility chain to

  \[
  \lambda\{x:a_nx\notin J\ (1\le n\le N)\}
   \le N^{-\tau/(\beta+1+4/R_N)+o(1)}+O(N^{-4});                       \tag{6}
  \]

- Lemma 5.6 and Proposition 5.7, paper pages 19--20, construct a separated
  subfamily \(\mathcal C_N\) of the equal partition into intervals of length
  \(s=M_N(\tau)^{-1}\), for \(0<\tau<1\).  If \(H\) is one member of
  \(\mathcal C_N\), or the union of two distinct members, Proposition 5.7
  gives uniformly in \(H\) the avoidance asymptotic

  \[
  \lambda\{x:a_nx\notin H\ (1\le n\le N)\}
    =\exp\{-N\lambda(H)+O((\log N)^{-3})\}.                            \tag{7}
  \]

The proof iterates survivor contraction over blocks using one- and two-point
estimates and Paley--Zygmund.  For the sharp lower bound it explicitly uses
the independent mixed-radix digits supplied by the divisibility chain.

For a fixed endpoint row,

\[
 X_e^\pm=\left\{\{(10^n-16)B_{M_e^\pm}\}:
                   M_e^\pm\le n\le U(M_e^\pm)\right\},                \tag{8}
\]

translation by \(-16B_M\) does not change the gaps, so this is the same
circular-gap problem as the finite dilated orbit
\(\{10^nB_M\}\) on that row.  The hypotheses fail at the decisive point:
\(B_M\) is a selected rational, not a Lebesgue-typical point, and changes
with \(M\).  Equations (5)--(7) bound the measure of exceptional starting
points; they provide no certificate that a particular \(B_M\) is outside the
exceptional set.  Thus (1) is strong methodological evidence, not a
specialization.

The empirical match is nevertheless exact at the scale level.  The frozen
[full-phase endpoint experiment](bbp_three_grid_full_phase_experiment_20260813.md),
SHA-256
`f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80`,
finds

\[
       0.899<\frac{L_eG_e^\pm}{\log L_e}<1.084
\]

on all twelve retained rows, up to \(L=610188\).  This remains an
`experiment`; Peres--Yang does not promote it.

## 4. Fractal transversality: a real drop, but not exclusion

Jiang--Li--Li--Wu,
[arXiv:2607.19813v1](https://arxiv.org/abs/2607.19813v1), Theorem 1.1,
paper page 3, assumes:

- \(E\) is generated by a homogeneous IFS
  \(\varphi_i(x)=\rho x+a_i\) satisfying the open set condition;
- \(0<\rho<1\) and \(\dim_H E<1\);
- \(f\) is a \(C^1\)-diffeomorphism; and
- \(\log|f'(x)|/\log\rho\notin\mathbb Q\) for every
  \(x\in E\cap f^{-1}(E)\).

It concludes

\[
                \overline{\dim}_{M}(f(E)\cap E)<\dim_H E.             \tag{9}
\]

For a base-10 missing-digit set and \(f(x)=16x+\alpha\), the logarithmic
condition holds because 16 and 10 are multiplicatively independent.  More
generally, an absent word of length \(m\) places the number in a homogeneous
base-\(10^m\) set with one aligned block deleted, and the same slope-16
condition holds.

This does not reach V1 for two independent reasons.  First, dimension drop
does not imply an empty intersection and therefore cannot exclude the named
point \(\{\pi\}\).  Second, missing a decimal word keeps the \(\times10\)
tails in the survivor; it does not say that
\(16\{\pi\}+\alpha\) lies in it.  For the actual invariant branch
\(f(x)=10x-k\), the ratio of logarithms is rational, so the theorem's
transversality hypothesis fails.

Their Theorem 1.4, paper page 5, is quantitative for
\(\gamma=(r/s)b^\ell\) subject to
\(|s|\ne r\), \(\gcd(s,r)=\gcd(sr,b)=1\).  With \(b=10\) and
\(\gamma=16\), \(\gcd(16,10)\ne1\); that quantitative theorem does not
apply.  The qualitative result (9) is the exact available conclusion.

## 5. Applicability matrix for the fresh sources

| Primary source and locator | Exact useful conclusion | Hypothesis that blocks a fixed-\(\pi\) application |
|---|---|---|
| Peres--Yang, [arXiv:2606.28860v1](https://arxiv.org/abs/2606.28860v1), Theorems 1.1--1.2, pp. 1--2; Propositions 4.3, 5.2, 5.7, pp. 14, 16, 20 | Maximal gaps have order \(\log N/N\) a.e.; sharp constant 1 for divisibility chains; uniform measure estimates for missing intervals | Lebesgue-a.e. fixed \(x\), not named \(\pi\) or the changing rational points \(B_M\) |
| Jiang--Li--Li--Wu, [arXiv:2607.19813v1](https://arxiv.org/abs/2607.19813v1), Theorems 1.1 and 1.4, pp. 3, 5 | Strict upper-Minkowski dimension drop for transverse affine copies; a quantitative bound under a coprimality condition | A drop may contain \(\pi\); decimal avoidance gives \(\times10\), not \(\times16\), joint membership; slope 10 is resonant; slope 16 fails Theorem 1.4's coprimality condition |
| Dai--Li--Wang--Wu, [arXiv:2606.25305v1](https://arxiv.org/abs/2606.25305v1), Theorem 1.4, p. 4 | For every target sequence \((x_n)\), \(0<\tau<\gamma/12\), and Cantor-measure-a.e. \(x\), the count of \(\|2^nx-x_n\|<n^{-\tau}\) has the expected asymptotic | Cantor-measure-a.e. point, not \(\pi\); support is the middle-third set |
| Dai--Li--Wang--Wu, same paper, Theorem 1.7, p. 5 | Analogous counting for a self-similar measure on \(K_{b,D}\), when \(b\) is prime, \(b\nmid t\), and \(0<\tau<\kappa\) | Still measure-a.e.; base 10 is not prime; no proof that \(\pi\) is typical for such a measure |
| Becher--Lew Deveali, [arXiv:2607.06773v1](https://arxiv.org/abs/2607.06773v1), Theorems 1--3, p. 2 | Uncountably many, and under computability hypotheses an explicit, points in a Hausdorff-dimension-zero sparse binary Cantor set that are normal in every odd base | Existence and Bernoulli-typicality do not identify a named special value; odd-base normality does not include base 10 |
| Manai, [arXiv:2606.08325v1](https://arxiv.org/abs/2606.08325v1), Theorems 1.1--1.2, pp. 1--2 | If independent binary digits have variance \(v_n\ge(\log n)^{\Gamma_0}n^{-(d-1)/d}\), then every degree-\(d\) polynomial image is a.s. absolutely normal; the critical power law can fail | Requires independent Bernoulli digits and a polynomial image; no such representation or probability law is known for \(\pi\) |
| Khalil--Luethi--Weiss, [arXiv:2502.19552v2](https://arxiv.org/abs/2502.19552v2), Theorems 1.1--1.2, pp. 2--3 | Equidistribution of pushed-forward Bernoulli carpet measures on lattice space under uniform non-divergence; Diophantine exceptional sets have measure zero | A statement about almost every point of a Bernoulli fractal measure and lattice dynamics, not the decimal orbit of a named point |
| Orr, [arXiv:2607.09565v1](https://arxiv.org/abs/2607.09565v1), Theorem 1.1 and Corollary 4.5, pp. 2, 17 | Explicit height bounds for algebraic inputs where G-function values satisfy a non-trivial global exact polynomial relation | A missing word gives approximate restricted-prefix statements, not a global exact relation at a moving algebraic input; the representation \(\pi=4\arctan(1)\) has fixed input of height zero |
| Kominers, [arXiv:2604.11282v1](https://arxiv.org/abs/2604.11282v1), Proposition 3.3 and Theorem 3.5, pp. 6--7 | Infinite missing-digit membership of a reduced rational \(r/Q\), \(\gcd(Q,m)=1\), bounds a fixed-prime valuation through \(\operatorname{ord}_{\operatorname{rad}(Q)}(m)\); yields finiteness for reciprocal sequences | BBP denominators contain base primes, shadows need only have finite legal prefixes, and V1 negation forbids an arbitrary word rather than necessarily one digit |
| Kwon, [arXiv:2502.10132v1](https://arxiv.org/abs/2502.10132v1), stated Bugeaud--Dubickas Theorem 1.1, p. 2 (article and addendum reposted in 2025) | For an integer \(\beta\ge2\) and irrational \(\xi\), the orbit \(\{\xi\beta^n\}\) cannot remain in an interval shorter than \(1/\beta\); equality is characterized by mechanical words | A one-word survivor is a union of many cylinders, not one containing interval; this only supplies coarse spread |

The sources on well-approximable/missing-digit intersections
([arXiv:2512.17173v1](https://arxiv.org/abs/2512.17173v1)), integer Cantor-set
arithmetic ([arXiv:2602.15292v1](https://arxiv.org/abs/2602.15292v1)), and
integers omitting digits in several bases
([arXiv:2503.09528v1](https://arxiv.org/abs/2503.09528v1)) were also checked.
Their conclusions concern dimensions, aggregate restricted-digit integers,
or constructed examples.  None selects \(\pi\) or the exact BBP endpoint
numerator, so they are not elevated into the main matrix.

## 6. Narrowest new route: a deterministic endpoint no-hit lemma

For even \(e\), retain the locally defined endpoint rows (8), their lengths
\(L_e^\pm\), and largest circular gaps \(G_e^\pm\).  The exact missing lemma
suggested simultaneously by the local experiment and Peres--Yang is:

> **Endpoint maximal-gap conjecture.**  There are constants \(C>0\) and
> \(e_0\) such that for every even \(e\ge e_0\) and
> \(\sigma\in\{-,+\}\),
> \[
>                    G_e^\sigma\le C\frac{\log L_e^\sigma}{L_e^\sigma}.
>                                                                    \tag{10}
> \]

This remains a `conjecture`.  It is exactly R5 of the current
[endpoint-gap recursion report](bbp_endpoint_gap_recursion_20260813.md),
whose present SHA-256 is
`6a4a8b77164acf76316e8effa197843d0b76629c9a596fa4b342742746d41c1d`.
Since \(L_e\to\infty\), (10) gives uniform circle coverage by every late row.
The established BBP tail estimate makes those rows shadow shifted decimal
orbit points with error tending to zero, and their exponents tend to
infinity.  Therefore (10) supplies the open premise of the T75 uniform-shadow
bridge.  The T75 implication to all repunit colors and then V1 is
`machine-checked`; its current independent audit is
[t75_uniform_shadow_cover_independent_audit.md](t75_uniform_shadow_cover_independent_audit.md),
SHA-256
`144cb3a2a83f63d633f68a5f4859cb363a93fed085cba8094284a4e9cc0cdf85`.

A proof should target a deterministic version of (6), not attempt to make
\(\pi\) generically random.  One operational form is:

\[
 \forall J\in\mathcal J_e,\quad
 \#\{n:M_e^\sigma\le n\le U(M_e^\sigma),
       \{(10^n-16)B_{M_e^\sigma}\}\in J\}>0,                         \tag{11}
\]

where \(\mathcal J_e\) is a circular mesh of intervals of length
\(\tau\log L_e/L_e\).  A count with main term
\(L_e|J|\asymp\log L_e\) and error \(o(\log L_e)\), uniformly in that mesh,
would suffice.

The local three-primary work explains what must be new in such a proof.  A
complete primary coordinate can supply exact averaging, but a generic
complementary CRT phase can saturate the selected Fourier coefficient.  Thus
length, multiplicative order, complete primary coverage, or Fourier support
alone cannot prove (11).  The estimate must exploit the **actual BBP endpoint
numerator** and its synchronized complementary phase.  The closest analogue
of the Peres--Yang block argument would:

1. partition the endpoint exponents into primary-compatible main blocks and
   buffers;
2. compute the first and second hit moments over the exact complete
   three-primary coordinate;
3. prove a BBP-specific bound for the selected complementary pair
   correlations, strong enough that every survivor block loses a fixed
   proportion; and
4. iterate for \(O(\log L_e)\) blocks to eliminate every interval in the
   mesh.

Step 3 is the genuine obstruction.  Replacing it by an arbitrary unit weight
is already ruled out by the local saturation separators.  Peres--Yang shows
that the block-survivor architecture and the target scale are right; it does
not supply this deterministic correlation estimate.

## 7. Search record, source pins, and coordination

The fresh search used primary arXiv manuscripts and exact PDF text.  It
covered 2025--2026 combinations of: named special values and E-/G-functions;
disjunctivity and subword complexity; missing-word and missing-digit sets;
Furstenberg transversality and fractal intersections; fixed-point and
shrinking-target lacunary orbits; maximal gaps; rational approximation with
restricted digits; and selected-numerator Fourier estimates.  A final arXiv
API pass over `math.NT`, `math.DS`, and `math.CA` submissions from
2026-08-06 through 2026-08-13 found no later applicable bridge.  Search
results and abstracts were used only to route the search; theorem claims
above were checked in the primary PDFs.

PDFs were fetched and hashed on 2026-08-13 UTC:

| Primary source/version | PDF SHA-256 |
|---|---|
| Peres--Yang, arXiv:2606.28860v1 | `bbfbd8b3cbcb0e4523873142eea72326f8d729c4cb2eeb58104741828688ac24` |
| Jiang--Li--Li--Wu, arXiv:2607.19813v1 | `a8714d9c504ecc31ca5398fbe4de1a93d102fedca93471690ed5dad3f9a23aff` |
| Dai--Li--Wang--Wu, arXiv:2606.25305v1 | `015a038b18559d23071488ab5a4397f5028a1699018507f0de6db64621a9f9a2` |
| Becher--Lew Deveali, arXiv:2607.06773v1 | `0ee221892c756ba8eda0e8cce591f44498410813be8d0eaa3c124fe4a6b390b1` |
| Manai, arXiv:2606.08325v1 | `52f332c672f92149476e77b2b92f9465bb6f4a17ae8542945cb23a69d040f2b0` |
| Khalil--Luethi--Weiss, arXiv:2502.19552v2 | `2e1e2cae6a37dc75610a0dbe10600b575501646500f34d358883277154cae190` |
| Orr, arXiv:2607.09565v1 | `df6e3f3843514d2e6ece4bf44db78a66095abbd211104f2743e58b43a8aaf732` |
| Kominers, arXiv:2604.11282v1 | `a7baf65c8f75e9de1caa17433d62898ab6d78b8d16182d7d12520e28dbd6637f` |
| Kwon, arXiv:2502.10132v1 | `e18ea115922d5154dcb5efe31e0e3c452389741216793e81772d2e8951fef29d` |
| Yavicoli--Yu, arXiv:2503.09528v1 | `c56dc8d1aa4ff873b62e02a483caaced8d2b04dd2c44d26e969adc11e7154d72` |
| Intersecting well approximable and missing digit sets, arXiv:2512.17173v1 | `bc69068e4f7394b4c3a52ea1c73268f250d3af81572c236a91390fea25d58e46` |
| Integer Cantor Sets, arXiv:2602.15292v1 | `a8106be4cedec874908e891fb2617c279d6b2966602c29de55ad1d990913e5b6` |

Proof-ledger watch
`watch:ultrapi:fresh-special-value-literature-20260813` was registered for
area `local:pi-digits`.  The initial and final polls both delivered no sibling
events through sequence 57401 (`cursor_seq = delivered_seq = 57401`,
`has_more = false`).  There was therefore no event to acknowledge.
Observation events, if later delivered, are coordination data only and do not
alter the claim status.

## Final status

The dated source audit is `literature-checked`.  The endpoint maximal-gap
statement (10), density of \(\{10^n\pi\}\), and canonical V1 remain
`conjecture`s.  The T75 conditional implication is `machine-checked`, but its
uniform-cover premise is not.  Nothing here is a `candidate resolution` or a
`verified resolution`.

The concrete progress is that the current experiment is no longer merely
heuristically "random-looking": a 2026 primary theorem proves the exact same
maximal-gap law for the corresponding divisibility-chain orbit at almost
every starting point and exposes a specific survivor-contraction method.
The remaining gap is now sharply localized to a deterministic,
BBP-numerator-specific substitute for its measure and mixed-radix
independence estimates.
