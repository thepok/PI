# T183: post-T177 concentration scout for overlapping iid block energy

Audit date: 2026-08-13 UTC. This is a bounded `literature-checked` audit of
the three source theorem statements in `SOURCE_LEDGER.csv`. The applications,
inequalities derived from them, and comparisons with unverified notes are
`proof sketch` mathematics. `verify_t183.py` is an `experiment` for exact
finite arithmetic, source locators, hashes, and package guardrails; finite
replay is not proof of a universal statement.

```text
PRIMARY_SOURCE_THEOREM_TUPLE_COUNT: 3
SEARCHED_DOMAIN_COUNT: 3
QUALIFYING_TUPLE_COUNT: 1
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 1
MODEL_SCOPE: iid related-model mathematics only
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
G11_CLAIM: none
G19_CLAIM: none
```

## 1. Scope, source statement, and ambiguities

The immutable canonical statement is vendored byte-for-byte as
`canonical_statement.txt`, SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks about strict circle-distance near returns for the prescribed fixed
orbit `{10^j*pi}`, with ordered pairs, diagonal included, and quantifiers
`for every A`, `for every sufficiently large n`, `there exists N`.

T183 does not alter or answer that question. It studies only the A10/A13/A14
sibling obtained from iid uniform decimal digits and exact equality of
overlapping blocks. Normalized ambiguities are:

1. `N` is the number of legal block starts, not the number of consumed digits.
2. Blocks overlap, do not wrap, and use digits through index `N+m-2`.
3. Energy counts ordered pairs and includes the `N` deterministic diagonals.
4. A tuple means one primary source and one named theorem together with the
   definitions and proof range needed to interpret it.
5. Previously unaudited means absent by stable ID, DOI, title, and author
   search from the supplied readable corpus. It is not a global novelty claim.
6. A theorem statement is literature-checked; every application below remains
   a proof sketch unless independently formalized.
7. Failure of a sufficient theorem is not evidence that the iid statistic
   lacks stronger concentration.

## 2. Exact model and expectation

Let `D={0,...,9}` and let `X_0,X_1,...` be independent and uniform on `D`.
For integers `N,m>=1`, put

```text
B_i^m=(X_i,...,X_(i+m-1)),                       0<=i<N,
c(w)=#{i<N:B_i^m=w},                             w in D^m,
E_m(N)=sum_w c(w)^2
      =sum_(0<=i,j<N) 1[B_i^m=B_j^m].            (2.1)
```

Fix `i<j` and let `h=j-i`. Equality means `X_r=X_(r+h)` for `m`
successive values of `r`. If `h<m`, the equality graph on the `m+h` hull
positions has exactly `h` residue-chain components, hence `10^h` satisfying
words among `10^(m+h)`. If `h>=m`, the `m` equality edges are disjoint and
the `h-m` gap coordinates are free, again giving `10^h` satisfying words.
Thus, including every overlapping lag,

```text
P(B_i^m=B_j^m)=10^(-m),                          i!=j. (2.2)
```

The `N` diagonal indicators equal one. Linearity, not independence of pair
indicators, now gives the exact ordered, diagonal-inclusive expectation

```text
E[E_m(N)] = N+N(N-1)10^(-m).                    (2.3)
```

## 3. Independently rederived McDiarmid baseline

Changing digit `X_t` changes only blocks with starts
`S_t={i<N:i<=t<=i+m-1}`; write `r_t=|S_t|<=m`. Only ordered pairs having at
least one endpoint in `S_t` can change. There are
`2r_t N-r_t^2` such pairs, and the `r_t` diagonal terms never change, so the
safe coordinate sensitivity is

```text
c_t <= 2mN.                                      (3.1)
```

For `m<=log_10 N` and `N>=2`, there are `N+m-1<=2N` digit inputs, whence

```text
sum_t c_t^2 <= 8m^2N^3.                          (3.2)
```

The vendored Lyons--Peres corrected edition, printed p. 457, Theorem 13.35,
text lines 23715-23731, states the independent-input one-sided inequality
`P(f-Ef>=u)<=exp(-2u^2/sum c_t^2)`.

Take `m>=m0(A)=min{m:10^m>=16A^2}` and `N>=4Am`. If `s=m0(A)`, then
`s<=2log_10(4A)+1<=4A`, so `10^s>=16A^2>=4As`. Since `10^m/m` increases for
integer `m>=1`, this proves the direct integer estimate `10^m>=4Am` for all
`m>=s`. Thus (2.3) gives

```text
E[E_m(N)] <= N^2/(2Am).                          (3.3)
```

Therefore failure of `E_m(N)<=N^2/(Am)` requires
`u=N^2/(2Am)`. Substitution in (3.2) gives exactly the requested computable
baseline

```text
P(E_m(N)>N^2/(Am)) <= exp(-N/(16A^2m^4)).        (3.4)
```

This derivation is independent of the unverified T177 note. It agrees with
that note's displayed baseline but imports no T177 deduction.

## 4. Bounded search: exactly three domains and tuples

The search stopped after one genuine primary-source theorem tuple in each of
exactly these three domains:

1. dependent or local U-statistics;
2. polynomial chaos or quadratic-form concentration;
3. entropy-method, self-bounding, read-k, or variance-sensitive martingales.

Searches by all three stable IDs, titles, and author strings found no occurrence
in the supplied readable knowledge corpus. Exact URLs, byte hashes, theorem
and proof locators, hypotheses, ranges, and all requested applicability fields
are in `SOURCE_LEDGER.csv`. There are exactly three tuples, within the required
range 3--6, and one tuple supports each domain.

## 5. S1: dependent U-statistics, exact transfer but structural constant loss

Duchemin--De Castro--Lacour Theorem 2 assumes a stationary uniformly ergodic
Markov chain, whole-space minorization, reverse Doeblin domination
`P(x,.)<=delta_M nu`, and bounded pi-canonical kernels. For every `u>0`, with
probability at least `1-beta exp(-u)log N`, it bounds the centered order-two
U-statistic by the explicit `A,B_N,C_N,u,N` expression at source text lines
410--416. The source asserts positive `beta,kappa` depending on chain
parameters; it does not make them numerical universal constants.

For the iid model, let `Y_i=B_i^m`. This is a stationary sliding-window Markov
chain on `D^m`, with `P^m(y,.)=pi`, the uniform law. The kernel
`h(y,z)=1[y=z]` is pi-canonical because its integral in either variable is
`10^-m`. Equations (2.2)--(2.3) give the exact transfer

```text
E_m(N)-E[E_m(N)]
 =2 sum_(i<j) (h(Y_i,Y_j)-E h(Y_i,Y_j)).          (5.1)
```

Thus growing `m`, overlap, all ordered pairs, the diagonal, and the target
deviation all transfer exactly. The fatal issue is theorem-class uniformity.
For every target state `z` there is a predecessor `y` with `P(y,{z})=1/10`.
Reverse Doeblin therefore forces

```text
1/10 <= delta_M nu({z}) for all 10^m states,
delta_M >= 10^(m-1).                             (5.2)
```

Uniform `nu=pi` attains equality. Hence no choice of dominating measure removes
the exponential growing-depth constant. Together with existential
`beta,kappa`, this cannot yield a computable uniform exponent with `gamma<4`
or the required depth ratio.

Classification: a **true in-class obstruction** for this reverse-Doeblin
theorem class, and also a proof-technique loss in its decoupling method. It is
not a transfer obstruction and not a true concentration obstruction for the
iid digit model.

## 6. S2: exact PSD quadratic form, exponential-rank screen

Hsu--Kakade--Zhang Theorem 1 assumes

```text
E exp(alpha'(x-mu)) <= exp(sigma^2||alpha||^2/2) for every alpha
```

and gives, for every `t>0`, an explicit `exp(-t)` upper tail for `||Ax||^2`
in terms of `tr(Sigma)`, `tr(Sigma^2)`, and `||Sigma||`, where
`Sigma=A'A`. All source constants are explicit.

Put `K=10^m`, `C=(c(w))_(w in D^m)`, and
`Z=C-(N/K)1`. Since `sum_w Z_w=0`, the all-pairs statistic has the exact PSD
encoding

```text
E_m(N)=N^2/K+||Z||_2^2.                          (6.1)
```

Overlap does not invalidate the source hypothesis. Color starts by residue
modulo `m`; blocks in one color are independent. Hoeffding's lemma in each
class and generalized Holder across the `m` classes give

```text
E exp(alpha'Z) <= exp(Nm||alpha||^2/4),          (6.2)
```

so `sigma^2=Nm/2` is valid. Applying the theorem on the sum-zero subspace,
where the projector has rank `K-1`, gives

```text
P(E_m(N)>N^2/K+(Nm/2)[K-1+2sqrt((K-1)t)+2t])
 <= exp(-t).                                     (6.3)
```

The smallest source threshold above `N^2/K` already contains
`(Nm/2)(10^m-1)`, far above the exact centered baseline and the required
`N^2/(Am)` scale in the relevant range. This is not merely a loose choice of
coordinates: the centered equality kernel on `D^m` has `K-1=10^m-1`
nonzero eigenvalues, so every exact inner-product/PSD representation has that
rank.

Classification: overlap causes a **transfer loss** of `m` in (6.2), isotropic
subgaussian compression is a **proof-technique obstruction**, and exponential
kernel rank is a **true in-class obstruction** for this exact PSD route. None
is a true obstruction to concentration of the iid statistic.

## 7. S3: generalized self-bounding transfer and gamma=3

Boucheron--Lugosi--Massart Definition 2 uses `a,b>0`, while Theorem 1 states
its result for `a,b>=0`. For independent inputs determining nonnegative
finite-mean `f`, the source's deletion certificate is

```text
0<=f-f_r<=1,    sum_r(f-f_r)<=a f+b,             (7.1)
```

and the theorem gives, for every `t>0`, with `c=(3a-1)/6`,

```text
P(f>=Ef+t)<=exp(-t^2/[2(aEf+b+c_+t)]).           (7.2)
```

All constants and ranges are explicit in the pinned source.

Let

```text
F_m(N)=sum_(0<=i<j<N) 1[B_i^m=B_j^m]
      =(E_m(N)-N)/2.                             (7.3)
```

For digit coordinate `r`, define `F_r` by deleting every pair whose union of
two block supports contains `r`. This is a measurable function of all inputs
except `X_r`. At most `m` starts contain `r`, hence

```text
0<=F_m-F_r<=mN.                                  (7.4)
```

Every colliding pair contributing to `F_m` is deleted once for each coordinate
in its two-block union support, which contains at most `2m` coordinates.
Therefore

```text
sum_r(F_m-F_r)<=2mF_m.                           (7.5)
```

Consequently `f=F_m/(mN)` satisfies Definition 2 with `a=2m` and every
`b>0`. Apply (7.2), rescale to raw deviation `u` for `F_m`, and then let
`b` decrease to zero in the continuous right-hand side. Since
`c_+=m-1/6`, this gives

```text
P(F_m-EF_m>=u)
 <= exp(-u^2/[4m^2 N EF_m+2m(m-1/6)N u]).       (7.6)
```

Under the same computable conditions `10^m>=4Am` and `N>=4Am`, (3.3) says
failure of the energy target requires `u=N^2/(4Am)`. Also
`EF_m=binom(N,2)10^-m<=N^2/(4Am)`. Substitution in (7.6), with safe
rounding upward of the denominator, yields

```text
P(E_m(N)>N^2/(Am))
 <= exp(-N/(24 A m^3))
 <= exp(-N/(24 A^2 m^3)).                        (7.7)
```

Thus `C=1`, `c=1/24`, and `gamma=3<4`, computably and uniformly for all
admissible integers. The source needs independence only of the underlying
digits; overlap and all collision dependence are handled by (7.4)--(7.5).
Ordering and the diagonal are restored exactly by (7.3).

This passes the strict gate. Better constants were not used to pass it.

## 8. Effective depth comparison

The mandated baseline depth is

```text
M0=floor((N/(64A^2 log N))^(1/4)).               (8.1)
```

Define the entirely effective integer depth

```text
M1=max({0} union {m>=1:96A^2m^3 ceil(log N)<=N}). (8.2)
```

For every admissible `m<=M1`, (7.7) is at most `N^-4`. For fixed `A`, direct
comparison of the cube-root and fourth-root scales gives

```text
M1/M0 asymptotic to
  (64^(1/4)/96^(1/3))*(N/(A^2 log N))^(1/12),    (8.3)
```

and hence `M1/M0 -> infinity`. Floors, ceilings, `m>=m0(A)`, and `N>=4Am`
affect only an effective finite onset. Therefore S3 also passes the alternative
depth-ratio gate. A union over at most `M1` depths costs only a polynomial
factor and remains effective on a standard exponentially growing prefix
schedule; no algorithmic-random point specialization is asserted here.

## 9. Complete applicability matrix

| tuple | growing m | overlap | all-pairs statistic | required deviation | constants | effectivity | uniformity | result |
|---|---|---|---|---|---|---|---|---|
| S1 dependent U-statistic | pointwise only | exact transfer | exact via (5.1) | represented | existential chain constants | fails uniformly | `delta_M>=10^(m-1)` | screened |
| S2 PSD quadratic form | theorem allows it but threshold explodes | transfer costs `m` | exact via (6.1) | threshold misses it | explicit | effective | rank `10^m-1` kills usefulness | screened |
| S3 self-bounding | yes | direct digit certificate | exact via (7.3) | `u=N^2/(4Am)` | `C=1,c=1/24,gamma=3` | effective | uniform under decidable conditions | qualifies |

Every requested applicability field is also a separate column in
`SOURCE_LEDGER.csv`.

## 10. Required normalized-fingerprint comparisons

`PRIOR_COMPARISON.csv` has exactly one row for each required comparator. The
verification boundary is essential: T144, T147, T152, T154, T161, T168,
T170, T172, and T177 are unverified notes or contain unverified deductions;
their notes only argue the listed fingerprints. They are comparison evidence,
not premises. T174 is active untrusted evidence with a `revise` skeptic result
for locator defects; no T174 claim is imported.

The nearest prior mechanisms are T150's separately-Lipschitz `m^4`
concentration, T177's McDiarmid `m^4` test, and T159's use of the same unordered
off-diagonal iid collision substrate for Palm--Stein approximation. T183 is
separate because it uses the decrement-sum certificate (7.4)--(7.5) to obtain
the direct `m^3` upper tail. Equality-graph ranks in T168--T172 are constraint
ranks for joint events, not S2's rank `10^m-1` of the centered equality kernel
as a linear operator. No novelty beyond this supplied-corpus nonduplication
boundary is claimed.

## 11. Scoped endpoint and successor

**SCOPED VERDICT (1/1): DEVELOP.** The literature-checked Boucheron--Lugosi--
Massart theorem and the proof-sketch deletion certificate give the exact
ordered, diagonal-inclusive overlapping iid decimal-block energy the uniform
computable bound (7.7), with `gamma=3<4`; (8.3) also gives the required
effective depth-ratio divergence. This verdict concerns iid related-model
mathematics only.

**BOUNDED SUCCESSOR (1/1, authorized after the verdict):** formalize the finite
deletion identities (7.3)--(7.5) and independently referee the rescaling from
the source theorem to (7.6)--(7.7). Do not schedule another broad concentration
scout unless that check finds a defect.

## 12. Explicit related-model and fixed-pi firewalls

Every conclusion in this report is **iid related-model mathematics**. The
underlying coordinates are independent uniform decimal digits. The decimal
digits of pi are not known to satisfy that premise. No theorem here applies to
the fixed orbit `{10^j*pi}`, and exact block equality is not the canonical
strict circle-distance event.

There is no fixed-pi claim, no A1 claim, no C1 claim, no C2 claim, no G11 claim,
and no G19 claim. Any fixed-pi use would require a separately proved transfer
that supplies the relevant product-space concentration or an equally strong
deterministic substitute for pi's actual digits, followed by a proved bridge
from exact blocks to the canonical metric count. Neither premise is asserted.

## 13. Self-contained replay

Inside a directory containing only these delivered artifacts, run:

```text
python3 verify_t183.py
```

The standard-library script checks hashes and source locators, exact lag
probabilities by finite enumeration, bounded-difference and self-bounding
certificates on small exhaustive instances, the algebra behind (7.7), all
domain/tuple/applicability counts, all twelve comparisons, the strict gate,
the single verdict and successor, and every firewall. Its output is pinned as
`raw_output.txt`.
