# T177: an effective multiscale collision test at a named random constant

Date: 2026-08-13 UTC.

Claim labels: only the rows marked `literature-checked` in
`SOURCE_LEDGER.csv` have been checked against pinned files and locators; rows
marked `bibliographic-only` are provenance, not checked theorem premises. The
derivation in Sections 3--9 is a `proof sketch`, not a machine-checked proof. Output from
`verify_t177.py` is an `experiment`: it checks finite instances, source pins,
constants, endpoints, and artifact integrity, but finite evidence is not a
proof. Section 12 is explicitly an `unproved pi-transfer` firewall.

```text
BASE: 10
DYADIC_PREFIX: N=2^n
KAPPA: 1
M0(A): ceil(2*log_10(4*A))
NAMED_POINT: Omega_U_CDS
SCOPED_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Canonical scope and normalized sibling

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question asks about strict metric circle near returns of the
fixed orbit `{10^j*pi}`. It counts ordered pairs, includes the diagonal, and
has the quantifiers `for every A`, `for every sufficiently large n`, `there
exists N`. This note does not change or answer it.

T177 is the A10/A13/A14 sibling in which:

1. `pi` is replaced by a named algorithmically random real;
2. circle distance is replaced by exact equality of decimal blocks;
3. only dyadic numbers `N=2^n` of legal starts are used; and
4. one conclusion is required simultaneously through logarithmic depth.

Exact block equality is weaker than metric near return. A theorem for one
algorithmically random real says nothing about the prescribed digits of pi
without an additional membership premise. The separation is load-bearing.

## 2. Exact definitions, endpoints, and quantifiers

Let `D={0,1,...,9}` and let

```text
X=(X_0,X_1,...) in D^(natural numbers)
```

be distributed by the uniform product measure `mu`; thus the coordinates are
independent and `mu(X_r=a)=1/10`. For integers `N>=1`, `m>=1`, define

```text
B_i^m(X)=(X_i,X_(i+1),...,X_(i+m-1)),       0<=i<N,
c_X(w;m,N)=#{i in {0,...,N-1}: B_i^m(X)=w}, w in D^m,
E_m(N;X)=sum_(w in D^m) c_X(w;m,N)^2
          =sum_(0<=i,j<N) 1[B_i^m(X)=B_j^m(X)].             (2.1)
```

Blocks overlap, do not wrap, and are not padded. There are exactly `N` legal
starts. The last block starts at `N-1`, ends at `N+m-2`, and hence (2.1)
depends on exactly the `N+m-1` digits `X_0,...,X_(N+m-2)`. The energy counts
ordered pairs and includes exactly `N` diagonal pairs.

Fix the named constants

```text
kappa=1,
m0(A)=ceil(2*log_10(4*A)),                    A integer, A>=1.   (2.2)
```

For effectivity, (2.2) is evaluated without real logarithms as
`m0(A)=min{m:10^m>=16*A^2}`. Likewise
`floor(log_10(2^n))=max{m:10^m<=2^n}`. These exact integer searches remove
rounding and equality-decision issues from the test enumeration.

The claim developed below is:

> For every Martin-Lof-random decimal sequence `X` and every integer `A>=1`,
> there is an effectively unspecified point-dependent integer `n_X(A)` such
> that, for every integer `n>=n_X(A)`, with `N=2^n`, and every integer
> `m0(A)<=m<=floor(log_10 N)`, one has
> `E_m(N;X)<=N^2/(A*m)`.

The test and all deterministic cutoffs used to build it are uniform and
computable in `A`; randomness supplies existence, not computation, of the
point-dependent last exceptional index.

If the interval in this display is empty, the assertion is vacuous. Eventually
it is nonempty for every fixed `A`.

## 3. Exact equal-block probability at every lag

Fix `0<=i<j<N` and put `h=j-i>=1`. Translate by `i`. The event
`B_i^m=B_j^m` is exactly

```text
X_r=X_(r+h), 0<=r<m,                            (3.1)
```

on the hull of `m+h` positions `0,...,m+h-1`.

If `1<=h<m`, the graph with these positions as vertices and edges
`{r,r+h}`, `0<=r<m`, consists of exactly `h` residue-class chains. The first
digit on each chain is free and every other digit is forced. Thus exactly
`10^h` of the `10^(m+h)` hull words satisfy (3.1).

If `h>=m`, the `m` edges are disjoint and the `h-m` gap positions are free.
There are `10^m*10^(h-m)=10^h` satisfying hull words. Consequently the same
formula holds at every positive lag, including every overlapping lag:

```text
P(B_i^m=B_j^m)=10^(-m),                         i!=j.          (3.2)
```

At lag zero, `P(B_i^m=B_i^m)=1`. Linearity of expectation, which requires no
independence among pair indicators, gives the exact ordered,
diagonal-inclusive mean

```text
E_mu E_m(N)=N+N*(N-1)*10^(-m).                  (3.3)
```

## 4. A uniform expectation margin

For `A>=1`, let `s=m0(A)`. Then

```text
10^s >= (4*A)^2,          s<=2*log_10(4*A)+1<=4*A.             (4.1)
```

The last inequality is elementary for `4*A>=4`. Hence `10^s>=4*A*s`.
The integer sequence `10^m/m` is increasing for `m>=1`, so for every `m>=s`,

```text
10^m>=4*A*m,  and therefore 10^(-m)<=1/(4*A*m).                (4.2)
```

If also `N>=4*A*m`, equations (3.3) and (4.2) imply

```text
E_mu E_m(N)
 <=N+N^2*10^(-m)
 <=N^2/(4*A*m)+N^2/(4*A*m)
 =N^2/(2*A*m).                                  (4.3)
```

This explicitly pays for the deterministic diagonal.

## 5. Overlap-sensitive bounded differences

Fix a digit coordinate `t` among `0,...,N+m-2`. Let

```text
S_t={i in {0,...,N-1}: i<=t<=i+m-1},   r_t=#S_t<=m.            (5.1)
```

Changing only `X_t` changes only blocks whose starts lie in `S_t`. Therefore
only ordered pairs `(i,j)` with `i in S_t` or `j in S_t` can change. There are
`N^2-(N-r_t)^2=2*r_t*N-r_t^2` such ordered pairs; their `r_t` diagonal
indicators never change. An exact safe count is therefore

```text
2*r_t*N-r_t^2-r_t<=2*m*N.                                     (5.2)
```

Pairs with both distinct starts in `S_t` must be retained: the changed digit
can occupy different offsets in their two blocks. The exhaustive replay
specifically checks this point.
Thus a coordinate bounded-difference constant is `c_t=2*m*N`.

For `m<=log_10 N` and `N>=2`, one has `m<=N` and `N+m-1<=2*N`. Hence

```text
sum_t c_t^2 <=(N+m-1)*(2*m*N)^2<=8*m^2*N^3.                   (5.3)
```

Lyons--Peres, corrected printed p. 457, Theorem 13.35, states the one-sided
bounded-differences inequality

```text
P(f-Ef>=u)<=exp(-2*u^2/sum_t c_t^2).                           (5.4)
```

McDiarmid's 1989 chapter is the primary provenance, but publisher access to
its full text was blocked in this session. No inaccessible internal locator is
asserted and no theorem statement is taken from it; (5.4) is checked against
the pinned, inspectable Lyons--Peres source.

Its hypotheses apply because the `N+m-1` input digits are independent and
(5.2) bounds the change under replacement of one digit. If `m>=m0(A)` and
`N>=4*A*m`, then (4.3) shows that

```text
E_m(N)>N^2/(A*m)
```

requires upward deviation at least `u=N^2/(2*A*m)`. Substitution in
(5.3)--(5.4) yields the explicit overlap-sensitive tail

```text
P(E_m(N)>N^2/(A*m))
 <=exp(-N/(16*A^2*m^4)).                      (5.5)
```

The fourth power of `m` is the visible price of using a bounded-differences
argument on overlapping blocks. No independence of block-pair indicators was
asserted.

## 6. Full logarithmic-depth union on dyadic prefixes

Put `N=2^n`. Every integer `m<=floor(log_10 N)` satisfies `m<=n`. Define

```text
d(A)=2*ceil(log_2(8*A)),
r(A)=min{n>=9: 2^n>=16*A^2*n^6},
n*(A)=max(d(A),r(A)).                           (6.1)
```

These are total computable integer functions. Finiteness of `r(A)` follows
from exponential domination; more explicitly, once its displayed inequality
holds at some `n>=9`, it persists because

```text
[2^(n+1)/(n+1)^6]/[2^n/n^6]=2*(n/(n+1))^6>1.                 (6.2)
```

To check the other cutoff, put `L=ceil(log_2(8*A))`, so `d(A)=2*L`.
Then `2^d>=64*A^2`, while `L<=log_2(8*A)+1<=8*A`; hence
`2^d>=8*A*L=4*A*d`. Since `2^n/n` increases for `n>=1`, every
`n>=d(A)` satisfies `2^n>=4*A*n`. Therefore `N>=4*A*m` throughout the
desired depth range. Define the finite bad event

```text
G_(A,n)={X: exists integer m with
  m0(A)<=m<=floor(log_10(2^n)) and
  A*m*E_m(2^n;X)>2^(2*n)}.                    (6.3)
```

The strict integer inequality in (6.3) removes any real-arithmetic ambiguity.
For `n>=n*(A)`, use (5.5), at most `n` candidate depths, and `m<=n`:

```text
mu(G_(A,n))
 <=n*exp(-2^n/(16*A^2*n^4))
 <=n*exp(-n^2)
 <=2^(-n).                                      (6.4)
```

For the last inequality, `log n-n^2<=-n*log 2` for `n>=2`.

## 7. Effectivity and summability

The event `G_(A,n)` depends only on the finite digit prefix through coordinate
`2^n+floor(log_10(2^n))-2`. Exhaustive evaluation of its integer predicate
makes it a uniformly computable finite union of clopen decimal cylinders. A
length-`L` cylinder has the exact rational measure `10^(-L)`. Thus both the
enumeration and every event measure are computable uniformly in `(A,n)`.

For fixed `A`, (6.4) gives

```text
sum_(n>=n*(A)) mu(G_(A,n))<=2^(-n*(A)+1).        (7.1)
```

Because `n*(A)>=2*ceil(log_2(8*A))`,

```text
2^(-n*(A)+1)<=1/(32*A^2).                       (7.2)
```

Consequently one single enumeration over all `(A,n)` is summable:

```text
sum_(A>=1) sum_(n>=n*(A)) mu(G_(A,n))
 <=sum_(A>=1) 1/(32*A^2)<infinity.              (7.3)
```

This convergence is effective. For example,

```text
sum_(A>Q) 1/(32*A^2)<=1/(32*Q),                 (7.4)
```

and, for the finitely many `A<=Q`, each geometric `n`-tail in (7.1) has a
computable cutoff. Thus the clopen sequence `(G_(A,n))` is a uniformly
effective Solovay test, not merely a null limsup proved nonconstructively.

If one insists on a conventional Martin-Lof test, for `a>=1` set

```text
K(A,a)=max(n*(A),a+A+2),
U_a=union_(A>=1) union_(n>=K(A,a)) G_(A,n).      (7.5)
```

Then `U_a` is effectively open and

```text
mu(U_a)<=sum_(A>=1) 2^(-a-A-1)=2^(-a-1)<2^(-a). (7.6)
```

If a sequence lies in infinitely many `G_(A,n)` for one fixed `A`, it lies in
every `U_a`. Therefore every Martin-Lof-random decimal sequence belongs to
only finitely many `G_(A,n)`, simultaneously for every integer `A>=1`.

## 8. Primary randomness and base-conversion sources

Hoyrup--Rojas, arXiv:0709.0907v2, printed pp. 23--27, supplies an inspectable
modern formulation of Martin-Lof tests and computable-space invariance:

1. printed p. 23 defines uniformly r.e. open tests with measure at most
   `2^(-n)` and random points as avoiding effective null sets;
2. Definition 6.1.1, printed p. 24, gives the equivalent integral-test form;
3. Proposition 6.2.1, printed p. 26, says computable probability-space
   morphisms are defined on random points and preserve randomness;
4. Corollaries 6.2.1--6.2.2, printed p. 27, give invariance under computable
   probability-space isomorphism and random expansions.

For completeness, the base-10 specialization is spelled out rather than
hidden in the citation. Let

```text
beta_b((d_i))=sum_(i>=0) d_i*b^(-(i+1)), b in {2,10}.          (8.1)
```

Each map is computable and sends the uniform digit product measure to
Lebesgue measure. Remove the effectively null endpoint sets consisting of
eventually-zero/eventually-`(b-1)` expansions and the corresponding rational
endpoints. Digit extraction is computable on the remaining full-measure
domain, so `beta_10^(-1) o beta_2` is a computable measure-space isomorphism
there. Proposition 6.2.1 and Corollary 6.2.1 transfer Martin-Lof randomness
from the binary expansion of a real to its unique decimal expansion.

Calude--Jurgensen, DOI `10.1007/3-540-58131-6_37`, pp. 44--66, is the primary
paper specifically titled *Randomness as an invariant for number
representations*. The author-hosted source is pinned as compressed PostScript
and its byte-exact decompression. Theorem 6.1 and Corollary 6.2, printed p. 61,
state invariance under transformations between natural positional
representations and then conclude that Martin-Lof randomness is invariant
among those representations. Thus it directly supports binary-to-decimal
conversion; Hoyrup--Rojas supplies the modern computable-probability-space
formulation and the explicit specialization above records the endpoint domain.

## 9. Named universal machine and named-point specialization

Fix `U_CDS` to be the compressed canonical register machine described by
Calude--Dinneen--Shu, arXiv:nlin/0112022v3, Section 5, printed pp. 6--10:

1. the instruction semantics are listed on printed pp. 6--7;
2. a valid program has exactly one terminal `HALT`, followed by binary data;
3. attempting to read beyond the data, leaving unread data, or using an
   undefined variable is a run-time error;
4. the grammar is specified on printed pp. 7--8;
5. canonicalization and the compressed 49-symbol format are specified on
   printed pp. 8--10; and
6. printed p. 9 states that the construction is universal in the algorithmic
   information-theory sense and self-delimiting.

Let `dom(U_CDS)` be its halting set under those conventions and define the
named constant

```text
Omega_U_CDS=sum_(p in dom(U_CDS)) 2^(-|p|).                  (9.1)
```

The paper's printed pp. 2--3 defines prefix-free machines and halting
probabilities. Theorem 2, printed p. 4, says that the halting probability of a
universal machine is c.e. and random; printed pp. 3--4 explicitly identify
their `random` with the equivalent Martin-Lof notion. Therefore the binary
expansion of `Omega_U_CDS` is Martin-Lof random. Section 8 transfers this to
its unique decimal expansion `X^CDS`.

Applying Section 7 to this named sequence gives, for every integer `A>=1`, an
integer `n_CDS(A)` such that for every `n>=n_CDS(A)`, with `N=2^n`, and every

```text
ceil(2*log_10(4*A))<=m<=floor(log_10 N),
```

one has

```text
E_m(N;X^CDS)<=N^2/(A*m).                       (9.2)
```

The paper states that full program and proof details for its computation would
appear elsewhere. T177 uses neither the claimed first 64 bits nor their
computation. It uses only the published machine conventions, asserted
universality, and the general halting-probability theorem. This caveat prevents
(9.1) from being misreported as a new formally verified machine construction.

## 10. Required comparisons and nonduplication

All conclusions attributed below to files under `notes/` remain conditional
on those unverified notes' arguments.

- **T2 (`machine-checked`).** T2 proves that base-10 normality of a generic
  symbolic orbit implies the canonical quantifier pattern for its ordered,
  diagonal-inclusive metric near-return count, and specializes it to
  Champernowne. T177 is distinct: it gives one named random point an explicit
  dyadic, simultaneous logarithmic-depth exact-block bound. It does not use
  T2 as a premise or turn normality into an effective rate.
- **T72 (`proof sketch`).** The T72 note argues that certain literal terminal
  Fejer top-shell/UPRID conditions are eventually false in a coupled Haar
  model under predetermined summable schedules. T177 instead constructs a
  successful effective exceptional-set test for a symbolic collision energy;
  no terminal phase condition is used.
- **T74 (`machine-checked`, different canonical problem).** T74 classifies a
  multiplier-nine coefficient fiber and shows coefficientwise cancellation
  fails in a pooled double-shift Laurent polynomial. T177 has no Fourier
  coefficientwise cancellation step, so that obstruction is orthogonal.
- **T144 (`proof sketch`) and T152 (`proof sketch`).** The T144 note argues a
  one-depth overlap-to-disjoint method-of-types census with `kappa=1/4`; the
  T152 note argues a maximal-bad-depth fractional-cover census. T177 neither
  imports those claims nor repeats their census: bounded differences directly
  handles all overlapping windows and the effective union reaches `kappa=1`.
- **T159 (`proof sketch`).** The note audits an unclustered Palm--Stein
  approximation and finds a nonvanishing same-lag excess. T177 seeks no
  Poisson approximation, only a bounded-differences upper tail.
- **T160 (`proof sketch`).** The report diagnoses pair-multiplicity loss in
  recurrence/Fourier routes and retains a deterministic Champernowne model.
  T177 uses neither recurrence charging nor Champernowne.
- **T161 (`proof sketch`).** The note tests same-lag chain declumping and closes
  one claimed sharper compound-Poisson approximation. T177 does not declump.
- **T162 (`proof sketch`).** The report proposes minimum-return separation as
  a deterministic sufficient condition. T177 assumes no minimum gap.
- **T163 (`proof sketch`, with pinned source statements).** The report screens
  GCD coverings, denominator shells, and independent-track cross-match
  energies. T177 uses a one-track iid product measure and none of those
  arithmetic fingerprints.
- **T164 (`proof sketch`).** The note argues primitive-substitution
  power-freeness/return separation. T177 concerns a named random sequence, not
  a substitution word.
- **T165 (`proof sketch`).** The note gives a coarse explicit deterministic
  Champernowne energy bound. T177's point is `Omega_U_CDS`, and its proof is
  exceptional-set rather than arithmetic-fiber counting.
- **T166 (`machine-checked`).** The module proves generic finite-word
  power-free separation and ordered collision packing. T177 imports no
  power-free hypothesis and is not a duplicate formalization.
- **T167 (`proof sketch`, with pinned source statements).** The report closes
  residue-interleaving entropy and algebraic-power repulsion candidates. T177
  uses neither candidate.
- **T168 (`proof sketch`).** The note exhibits mixed-lag cluster families that
  obstruct raw cluster negligibility. Bounded differences allows arbitrary
  dependence among collision indicators, so T177 does not assume that
  negligibility.
- **T169 (`proof sketch`).** The note sharpens deterministic Champernowne
  energy to a `1+O(1/K)` asymptotic. It concerns a different named point and a
  different counting mechanism.
- **T170 (`proof sketch`).** The note derives a positive third-cumulant lower
  bound. T177 makes no Gaussian or low-cumulant approximation.
- **T171 (`literature-checked` sources; screens are `proof sketch`).** The
  scout closes automatic-correlation, restricted-denominator, and
  self-similar-Fourier candidates for the fixed-pi frontier. T177 is an
  algorithmic-randomness sibling and reserves none of those tuples.
- **T172 (`proof sketch`).** The note gives a fourth-order overlapping-tail
  nonabsorption witness against occupancy-only clique moments. T177 keeps the
  full energy as a function of independent digits and does not replace its
  dependence by occupancy-only moments.

Thus none of T159--T172 supplies or is duplicated by this effective
algorithmic-randomness test.

The current snapshot contains T166's machine-checked finite-word theorem and
T171's report; older notes describing either as unavailable are stale. T74 is
available in the workspace and axiom audit but belongs to the separate
`pi-long-lag-block-collision-decay` program. These are availability and
duplication boundaries, not promoted mathematical premises.

## 11. Scoped endpoint

**SCOPED VERDICT: HOLD AS MODEL.** The `proof sketch`, with the cited
literature premises, gives the named decimal expansion of `Omega_U_CDS` the
eventual bound (9.2) simultaneously through logarithmic depth on every dyadic
prefix. This is a related-model statement about exact block equality. It is
not a fixed-pi result and is not a claim about A1, C1, or C2.

## 12. Explicit unproved pi-transfer firewall

**`unproved pi-transfer`:** to apply this mechanism to pi, one would have to
prove the additional premise that the canonical decimal expansion of pi
avoids the specific uniformly effective Solovay test `(G_(A,n))` constructed
in (6.3) and enumerated over all `A>=1`, `n>=n*(A)`. No source or argument here
proves that premise. Pi is not known to be Martin-Lof random, and ordinary
irrationality, conjectural normality, or finite digit data does not establish
avoidance of this test. Even that premise would directly yield only the A10
exact-block sibling; a separate proved bridge would still be needed for the
canonical metric count. Therefore T177 makes no fixed-pi, A1, C1, or C2 claim.

## 13. Replay

Inside a directory containing only the delivered artifacts, run:

```text
python3 verify_t177.py
```

The script uses only the Python standard library and local files. It checks
the canonical and source hashes, source locators, exact lag counts on bounded
instances, bounded-difference sensitivity on exhaustive small instances,
the named constants over a substantial finite range, report guardrails, and
manifest integrity. Its output must equal `raw_output.txt` byte for byte.
