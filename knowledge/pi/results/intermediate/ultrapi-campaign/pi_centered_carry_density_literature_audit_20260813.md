# Fixed-pi centered-carry density and BBP empirical-measure audit

Audit date: **2026-08-13 UTC**

Status: `literature-checked` bounded primary-source audit, with the new
applications below labeled `proof sketch`

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt), SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

## Outcome

No checked theorem proves linear lower density of the nonzero centered
decimal carries of \((10^P-1)\pi\), produces an infinite-support empirical
limit for the fixed decimal orbit of pi, or supplies the BBP
nonsingularity/matching premise.  No proof that every finite decimal word
occurs in pi was obtained.  Canonical V1 remains a `conjecture`.

There are two exact and useful boundary results.

1. Chen--Ye--Zheng's April 2026 theorem applies pointwise to
   \(x_n=(10^P-1)\pi10^n\).  It gives a uniform topological excursion
   \(\limsup_n\|x_n\|\ge1/11\), an infinite omega-limit set, and a
   progression-slice spread statement.  It therefore forces nonzero centered
   carries at arbitrarily large indices, with errors bounded away from zero.
   It gives no visit count, density, Cesaro mass, or empirical support.
2. Mahler's 1973 multiplier theorem says that for every block length \(m\),
   some bounded integer multiplier \(X_m\) makes \(X_m\pi\) contain every
   length-\(m\) word infinitely often.  The multiplier may depend on \(m\)
   and is not forced to be \(1\) or a repunit \(10^P-1\).  This is a sharp
   quantifier mismatch, not a result about the digit language of pi itself.

The strongest checked quantitative bound for the actual centered carries
remains logarithmic:

\[
 \liminf_{N\to\infty}{K_P(N)\over\log N}
 \ge {1\over\log(888/125)}.
\]

The desired fixed-period BBP criterion requires \(K_P(N_j)=\Omega_P(N_j)\)
for every fixed \(P\), on one common subsequence \(N_j\).  The missing factor
\(N/\log N\) remains.

## 1. Exact target and empirical bridge

For \(P\ge1\), put \(q_P=10^P-1\) and define

\[
 z_{P,n}=\left\lfloor q_P10^n\pi+\frac12\right\rfloor,
 \qquad
 e_{P,n}=q_P10^n\pi-z_{P,n}\in(-1/2,1/2),
\]

\[
 \gamma_{P,n}=z_{P,n+1}-10z_{P,n}
              =10e_{P,n}-e_{P,n+1}\in\{-5,\ldots,5\},
\]

and

\[
 K_P(N)=\#\{0\le n<N:\gamma_{P,n}\ne0\}.
\]

There is no nearest-integer tie because pi is irrational.  The frozen carry
audit proves, at `proof sketch` status and with a passing independent audit,
that for every prescribed \(N_j\to\infty\),

\[
 \liminf_j {K_P(N_j)\over N_j}>0
 \quad\Longleftrightarrow\quad
 \liminf_j {1\over N_j}\sum_{n<N_j}
       \|q_P10^n\pi\|_{\mathbb T}^2>0.                 \tag{1}
\]

The quantifiers needed by the current BBP route are

\[
 \exists (N_j)\to\infty\ \forall P\ge1:\quad
 \liminf_j K_P(N_j)/N_j>0.                            \tag{2}
\]

The bound may depend on \(P\), but the subsequence may not.

There is an exact empirical formulation of the missing statement.  Let

\[
 \mu_N={1\over N}\sum_{n<N}\delta_{\{10^n\pi\}}.
\]

If \(\mu_{N_j}\Rightarrow\mu\), weak convergence and continuity give

\[
 {1\over N_j}\sum_{n<N_j}\|q_P10^n\pi\|_{\mathbb T}^2
 \longrightarrow
 \int_{\mathbb T}\|q_Px\|_{\mathbb T}^2\,d\mu(x).    \tag{3}
\]

The integrand's zero set is the finite subgroup
\(q_P^{-1}(0)\).  Consequently an infinite-support weak limit \(\mu\) would
make the right side of (3) positive for every \(P\), simultaneously on the
same \(N_j\), and (1) would yield (2).  This is why an infinite-support
empirical theorem would be decisive.  An infinite **topological** omega-limit
set is not such a theorem.

## 2. Direct application of Chen--Ye--Zheng

The primary source is Chen--Ye--Zheng,
[*Distribution modulo one of linear recurrent sequences*](https://arxiv.org/abs/2604.14036v1),
arXiv:2604.14036v1, submitted 15 April 2026.  The exact locators are Theorem
1.3 on paper page 2, Remark 1.4 on pages 2--3, and Corollary 3.4 with Remark
3.5 on paper page 10.  The following specialization is a `proof sketch`.

Fix \(P\), set \(\xi=q_P\pi\), and take

\[
 x_n=\xi10^n,\qquad R(T)=T-10.
\]

Then \(x_{n+1}-10x_n=0\), \(L(R)=11\), and the representation in the source
has one algebraic root \(\alpha=10\) and one constant coefficient polynomial
\(F=\xi\).  Since
\(\mathbb Q(10)=\mathbb Q\) and \(\xi\notin\mathbb Q\), condition (c′) of
Theorem 1.3 holds.  Its conclusions specialize to:

\[
 \omega(\{q_P\pi10^n\bmod1\})\text{ is infinite},
 \qquad
 \limsup_{n\to\infty}\|q_P\pi10^n\|_{\mathbb T}\ge {1\over11}. \tag{4}
\]

Corollary 3.4, with \(p_1=10,q_1=1\), and Remark 3.5 additionally give:
for every \(M\ge1\), some residue \(0\le r<M\) has a progression-slice
omega-limit set not contained in any circle interval of length less than
\(1/10\).  The source initially permits \(l\ge0\); replacing \(l\) by its
residue modulo \(M\) changes only a finite prefix.

Equation (4) has a direct carry consequence.  If
\(\gamma_{P,n}=0\), then \(e_{P,n+1}=10e_{P,n}\), hence

\[
 |e_{P,n}|<1/20.                                      \tag{5}
\]

Because \(1/11>1/20\), (4) forces infinitely many \(n\) with
\(\gamma_{P,n}\ne0\).  The mere infinitude of the carries already follows
from irrationality; the new content is the fixed-amplitude topological
excursion and progression-slice spread.

The theorem contains no lower bound for the number of indices realizing an
excursion.  Its quantifier is “for every progression modulus, there exists a
slice whose **limit set** has a given spread,” not “a positive proportion of
indices visits two separated regions.”  It therefore does not imply (2) or
positive mass in (3).

### Exact logical separator

This gap is not terminological.  Concatenate the dyadic grids

\[
 D_s=\{j/2^s:0\le j<2^s\}
\]

to obtain a sequence \((a_k)\) every tail of which is dense in the circle.
Define \(y_n=a_k\) when \(n=k!\), and \(y_n=0\) otherwise.  For every fixed
\(M\), all sufficiently late \(k!\) lie in the zero residue class modulo
\(M\), so that progression slice has the full circle as its omega-limit set.
Also \(\limsup\|y_n\|=1/2\).  Nevertheless

\[
 {1\over N}\sum_{n<N}\delta_{y_n}\Rightarrow\delta_0,
\]

because the factorial times have density zero.  Thus even the shapes of all
three Chen conclusions coexist with a one-point empirical limit.  This
separator is not a decimal orbit and does not challenge the source theorem;
it proves only that its conclusions cannot be converted into frequency or
empirical support without an additional orbit-specific argument.

## 3. The closest all-word theorem has the multiplier outside the target

Mahler,
[*Arithmetical properties of the digits of the multiples of an irrational
number*](https://doi.org/10.1017/S000497270004243X), Bull. Austral. Math.
Soc. **8** (1973), 191--203, Theorem 2 on printed pages 202--203, proves the
following quantified statement in every integer base \(g\ge2\): for an
irrational \(\alpha\) and a fixed word length \(m\), there is a positive
integer \(X\), bounded in terms of \(g,m\) independently of \(\alpha\), such
that the base-\(g\) expansion of \(X\alpha\) contains every length-\(m\) word
infinitely often.

For decimal pi, this gives

\[
 \forall m\ \exists X_m\ \forall w\in\{0,\ldots,9\}^m\
 \exists^\infty n:\quad w\text{ occurs at }n\text{ in }X_m\pi. \tag{6}
\]

Canonical V1 instead requires

\[
 \forall m\ \forall w\in\{0,\ldots,9\}^m\ \exists n:\quad
 w\text{ occurs at }n\text{ in }\pi.                 \tag{7}
\]

Nothing in Mahler's theorem sets \(X_m=1\), makes the multipliers independent
of \(m\), or places them in the repunit family \(10^P-1\).  The paper also
constructs irrational inputs showing that no universal theorem can simply
fix one multiplier and retain all of this conclusion.  Special arithmetic
information about pi would be needed to pass from (6) to (7).

## 4. Strongest quantitative carry bound remains logarithmic

Zeilberger--Zudilin prove
\(\mu(\pi)\le7.103205334137\ldots<888/125\).  The frozen centered-carry
audit applies this to gaps between consecutive nonzero carries and obtains,
for every fixed \(P\),

\[
 \liminf_{N\to\infty}{K_P(N)\over\log N}
 \ge {1\over\log(888/125)}=0.5100328548\ldots .       \tag{8}
\]

It also transfers the bound to the exact rational BBP defect energy:

\[
 \liminf_{N\to\infty}{1\over\log N}
 \sum_{n<N}\|(10^P-1)u_n\|_{\mathbb T}^2
 \ge {1\over121\log(888/125)}.                       \tag{9}
\]

These deductions remain a `proof sketch`; their frozen independent audit and
exact replay pass.  Rivoal's 2008 paper on the binary bits-counting function
records the same general logarithmic scale for any real with finite
irrationality exponent.  It counts ordinary binary ones, not centered decimal
carries, and supplies no stronger pi-specific input.

Rivoal also isolates the potentially stronger exponent obtained when
denominators are restricted to powers of the base.  No checked source gives
a useful pi-specific base-10 restricted exponent beyond what follows from
the general irrationality measure.  Even the optimal algebraic-style
restricted exponent controls sparse digits rather than providing the linear
frequency in (2).

The Kempner--Fredholm separator in the frozen carry audit has finite optimal
irrationality exponent but only \(\Theta_P(\log N)\) defect energy.  Hence a
finite scalar irrationality measure, even an optimal one, cannot by itself
justify the jump from (8) to linear density.

## 5. BBP, automatic, and lacunary routes

| route | exact checked hypothesis or conclusion | fixed-pi obstruction |
|---|---|---|
| Bailey--Borwein--Plouffe | Supplies the exact base-16 four-pole series and rational partial sums. | No orbit-distribution or empirical-support theorem. |
| Bailey--Crandall 2001/2002 | Normality/density conclusions use their explicitly stated Hypothesis A. | The hypothesis remains unproved; it cannot be treated as a theorem about pi. |
| Lagarias, arXiv:math/0101055v2 | Unconditional shadowing and rationality/finite-limit-set results; digit density and normality in Theorem 4.1 require weak/strong dichotomy hypotheses. | No positive Cesaro mass or fixed-pi matching.  Hexadecimal/base-2 density would not imply decimal disjunctivity. |
| BBP empirical limits | The frozen audit proves that the diagonal BBP empirical measures and the actual decimal-orbit empiricals have the same weak limits, all \(T_{10}\)-invariant. | It proves neither infinite support, nonatomicity, ergodicity, nor nonsingularity with the \(T_{16}\)-pushforward. |
| Bell--Chen finite-alphabet D-finite theorem | If the decimal digit series of pi were D-finite, it would be rational, contradicting irrationality of pi. | Therefore the digit series is not D-finite; forbidden-word sequences can also be non-D-finite, so this is no density theorem. |
| automatic/Mahler word theorems | Automatic and strongly repetitive expansions often imply rationality or transcendence; Nguyen's 2026 refined exponent strengthens this forward direction. | Pi is already transcendental.  The implications cannot be reversed to infer recurrence, automaticity, or carry density from transcendence. |
| recent lacunary covering/gap results | Stefanescu, arXiv:2504.03575v5, proves results for Lebesgue-almost every dilation and measures with Fourier decay.  Hauke--Shubin--Stefanescu--Zafeiropoulos, arXiv:2604.02005v1, likewise treats random multipliers and Fourier-decaying measures. | A fixed point mass at pi is not an almost-everywhere conclusion and has Fourier transform of modulus one, so it does not meet positive Fourier-decay assumptions. |
| Host/Hochman/Rudolph rigidity | Applies after invariant, ergodic, positive-entropy or common-invariance/typical-point hypotheses are established. | The named point pi and its BBP empirical limits are not supplied those hypotheses. |

The August 2026 computational papers on large prefixes of pi remain
`experiment`: finite statistical agreement cannot establish an asymptotic
frequency or a future word occurrence.

## 6. Exact missing inputs

Either of the following would materially close the current carry branch:

1. one subsequence \((N_j)\) and a weak limit of \(\mu_{N_j}\) with infinite
   support, which by (3) handles every fixed \(P\) on that same subsequence;
2. a direct pi-specific estimate \(K_P(N_j)\ge c_PN_j\) for all fixed \(P\)
   on one common subsequence;
3. the alternative empirical-rigidity premise from the frozen BBP audit: an
   appropriate decimal empirical limit that is ergodic, nonatomic, and not
   mutually singular with its \(T_{16}\)-pushforward; or an equivalent
   all-depth affinity/matching estimate.

Chen supplies topological spread, Mahler supplies a movable multiplier,
Zeilberger--Zudilin supplies scalar rational separation, and BBP supplies
exact rational shadowing.  None supplies one of these frequency or measure
inputs.

## 7. Mathlib audit

The bounded local search used mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (`v4.30.0`).  It found:

- `LiouvilleWith` and rational/integer-multiple invariance in
  `Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean`;
- almost-everywhere non-Liouville statements in
  `Mathlib/NumberTheory/Transcendental/Liouville/Measure.lean`;
- `AddCircle.ergodic_nsmul` for circle volume in
  `Mathlib/Dynamics/Ergodic/AddCircle.lean`; and
- abstract support monotonicity under absolute continuity in
  `Mathlib/MeasureTheory/Measure/Support.lean`.

These are useful interfaces, but the almost-everywhere and volume-measure
theorems do not make the named point pi typical.  No theorem for pi's
irrationality exponent, decimal normality/disjunctivity, centered-carry
density, a fixed lacunary orbit, or BBP empirical nonsingularity was found.
No Lean declaration was added, so no theorem was registered in
`audit/AxiomAudit.lean` and no formal verification gate was run for this
literature report.

## 8. Source pins, checker, and bounded-search record

The core PDFs and frozen input audits are pinned by the companion checker.

| source/artifact | exact version or locator | SHA-256 |
|---|---|---|
| Chen--Ye--Zheng | arXiv:2604.14036v1 | `a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d` |
| Mahler | Bull. Austral. Math. Soc. 8 (1973), DOI PDF, Theorem 2 | `263facae776cfc081d99eafc3ab93e29ebc4b213482c0a9adc97342aa99b7288` |
| Rivoal | J. Aust. Math. Soc. 85 (2008), DOI 10.1017/S1446788708000591 | `060032757c32e146078c542e72c793aaaf854b48cf264517493ff7d77a3a690e` |
| Zeilberger--Zudilin | Moscow J. Comb. Number Theory 9 (2020), 407--419 | `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` |
| Lagarias | arXiv:math/0101055v2 | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Bailey--Borwein--Plouffe | 1997 primary PDF | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Bailey--Crandall | 2001 primary PDF | `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` |
| Bailey--Crandall | 2002 primary PDF | `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74` |
| frozen centered-carry report | 2026-08-13 | `bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55` |
| centered-carry independent audit | 2026-08-13 | `ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91` |
| frozen BBP empirical report | 2026-08-12 | `80fc0a6f9bd159dc36438a78ec10b35c76b433c2bae084750b3c34199d97534c` |
| BBP empirical independent audit | 2026-08-12 | `33cf4c1224dffa7d019e38fe82bbd0ed352187ba6b1e4548e1109b459961e1ac` |
| companion checker | 2026-08-13 | `0f1c2d396dee752232dc55b3bc5deacdfff2e5404153afb2fe2ada1cd71fc8c4` |

Run the checker with:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/pi_centered_carry_density_literature_audit_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/pi_centered_carry_density_literature_audit_20260813_check.py
```

The retained run reports `PASS`.  Its source-marker checks and rational
identity replays are an `experiment`; they do not elevate any infinite claim.

Searches through **2026-08-13 UTC** covered combinations of fixed-pi digit
changes, nonzero digits of pi and rational multiples, base-10 restricted
irrationality, BBP empirical measures and joinings, fixed lacunary orbits,
automatic/Mahler/holonomic digit complexity, and 2025--2026 follow-ups.  The
recent exact version pins additionally checked were
[Stefanescu arXiv:2504.03575v5](https://arxiv.org/abs/2504.03575v5),
[Hauke et al. arXiv:2604.02005v1](https://arxiv.org/abs/2604.02005v1),
[Nguyen arXiv:2605.30606v2](https://arxiv.org/abs/2605.30606v2), and
[Bell--Chen arXiv:1606.04986v1](https://arxiv.org/abs/1606.04986v1).
This is a bounded applicability audit, not an exhaustive-absence or novelty
claim.

## Bottom line

The new direct theorem for \(q_P\pi10^n\) reaches fixed-pi topological
noncollapse with explicit constants, but not frequency.  Mahler reaches all
words infinitely often only after moving to a block-length-dependent
multiple of pi.  The quantitative fixed-pi carry theorem still stops at
\(\Omega(\log N)\), whereas the current route needs \(\Omega_P(N)\) on one
common subsequence, equivalently an infinite-support empirical limit or a
comparably strong nonsingularity/matching input.  No checked source supplies
that missing step, so V1 remains a `conjecture`.
