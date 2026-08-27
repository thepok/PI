# T187: fractional deletion obstruction for overlapping iid block energy

Audit date: 2026-08-13 UTC. This is a `proof sketch` note with one
`literature-checked` primary theorem tuple. The finite replay is an `experiment`
for falsification only. No Lean theorem is claimed.

```text
PRIMARY_SOURCE_THEOREM_TUPLE_COUNT: 1
SOURCE_CAP: at most 6
CERTIFICATE_COUNT: 1
SCOPED_RELATED_MODEL_VERDICT_COUNT: 1
MODEL_SCOPE: iid related-model mathematics only
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable question, sibling scope, and ambiguities

The canonical source is local, not an external URL:
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its byte-exact vendored
copy `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks whether every integer `A>=1` has an `n0` such that every `n>=n0`
admits `N>=1` with `A*n*Q_pi(n,N)<=N^2`, for strict circle-distance near
returns of the fixed orbit `{10^j*pi}`; pairs are ordered and the diagonal is
included.

T187 does not alter or answer that question. It studies only the A10/A13/A14
sibling obtained from iid uniform decimal digits and exact equality of
overlapping blocks. Ambiguities are fixed as follows.

1. Integers `N>=2`, `m>=1`, and `A>=1` are parameters. `N` is the number of
   legal block starts, not the number of digits.
2. There are exactly `L=N+m-1` input digits, indexed `0,...,N+m-2`.
3. Blocks do not wrap or pad. The final block starts at `N-1` and has inclusive
   endpoint `N+m-2`, the final supplied digit.
4. The energy counts ordered pairs and includes all `N` deterministic diagonal
   pairs. The deletion certificate is stated on unordered off-diagonal pairs,
   then converted exactly back to energy.
5. The proposed certificate below was fixed before calculation. No alternative
   certificate is substituted after its failure.
6. A theorem tuple is one primary source plus one named theorem and its
   load-bearing definitions. Only one tuple is inspected, within the cap six.
7. The declared logarithmic-depth range is
   `N>=100`, `1<=m<=floor(log_10 N)`. The obstruction actually holds for every
   `N>=2,m>=1`, so it is uniform on this nonempty range.
8. Finite computation can falsify identities or implementation claims but is
   not a proof of any universal claim.

## 2. Exact energy and expectation conventions

Let `D={0,...,9}` and let `X_0,...,X_(N+m-2)` be independent and uniform on
`D`. For `0<=i<N`, define the inclusive block support and word

```text
I_i={i,...,i+m-1},
B_i^m=(X_i,...,X_(i+m-1)).                                  (2.1)
```

For `w in D^m`, put `c(w)=#{i<N:B_i^m=w}` and

```text
E_m(N)=sum_w c(w)^2
      =sum_(0<=i,j<N) 1[B_i^m=B_j^m].                      (2.2)
F_m(N)=sum_(0<=i<j<N) 1[B_i^m=B_j^m]
      =(E_m(N)-N)/2.                                       (2.3)
```

Thus (2.2) is ordered and diagonal-inclusive; (2.3) removes only the
deterministic diagonal and one of the two off-diagonal orientations. For every
`i<j`, the equality graph has probability `10^-m`, including when blocks
overlap: on the `m+(j-i)` hull positions its equality edges have `j-i`
residue-chain components. Hence, by linearity,

```text
E[E_m(N)]=N+N(N-1)10^-m,
E[F_m(N)]=binom(N,2)10^-m.                                 (2.4)
```

No independence among collision indicators is asserted.

## 3. The one precommitted certificate

For `i<j`, let

```text
S_ij=I_i union I_j,              m<=|S_ij|<=2m.             (3.1)
```

The proposed **fractional support-deletion certificate** allocates each
realized collision equally over the digit coordinates in its union support:

```text
d_r(X)=sum_(0<=i<j<N)
         1[B_i^m=B_j^m] * 1[r in S_ij]/|S_ij|,             (3.2)
F_r^frac(X)=F_m(N;X)-d_r(X).                               (3.3)
```

This proposal is attractive because the allocation identity is exact:

```text
sum_(r=0)^(N+m-2) d_r(X)=F_m(N;X).                         (3.4)
```

Indeed, every active pair contributes `1/|S_ij|` at each of its `|S_ij|`
support coordinates. If (3.3) were a legal coordinate-deleted surrogate, then
after scaling by a one-coordinate drop bound `C` the generalized
self-bounding coefficient from the decrement sum would be `a=1`, rather than
the whole-support multiplicity coefficient proportional to `m` in T183. At
the target deviation scale this is exactly the prospective route to remove an
`m` loss and seek `gamma<3`. This paragraph is motivation, not a claimed tail
bound.

The certificate is now tested without changing it.

## 4. The sole source tuple and every hypothesis

`SOURCE_LEDGER.csv` pins the only inspected tuple: Boucheron--Lugosi--Massart,
*On concentration of self-bounding functions*, EJP 14 (2009), DOI
`10.1214/EJP.v14-690`. The exact versioned retrieval URL, PDF/text hashes, and
locators are in that ledger.

The source's coordinate-deletion notation appears at printed p. 1885/text line
79: `x^(i)` is obtained by dropping coordinate `i`. Lines 94--103 give a standard
choice `f_i(x^(i))=inf_(x_i') f(...)` and explicitly require measurability.
Definition 2, printed pp. 1885--1886/text lines 108--117, requires, for each
coordinate, a function `f_i` on the dropped-coordinate input satisfying

```text
0<=f(x)-f_i(x^(i))<=1,
sum_i(f(x)-f_i(x^(i)))<=a*f(x)+b.                          (4.1)
```

Theorem 1, printed pp. 1886--1887/text lines 160--183, assumes independent
inputs, a nonnegative measurable finite-mean `f`, and the certificate (4.1),
then gives the displayed upper tails for all `t>0`.

Parameter substitution and status are exhaustive:

| source requirement | T187 substitution | status |
|---|---|---|
| independent inputs | the `L=N+m-1` iid uniform digits | passes |
| nonnegative measurable finite-mean statistic | `F_m(N)/C` on a finite product space, for any `C>0` | passes |
| one surrogate on input with coordinate `r` dropped | proposed `(F_m-d_r)/C` | **fails** |
| `0<=f-f_r<=1` | would require a chosen scale `C>=max d_r` | not reached |
| positive parameters `a,b` in Definition 2 | choose `a=1` and any `b>0`; then (3.4) would give `sum_r(f-f_r)=f<=f+b` | algebraically passes but unusable |
| theorem range | every `t>0` after all hypotheses | not reached |

Scaling cannot repair the failed row: multiplying `(F_m-d_r)` by any fixed
nonzero constant does not make it independent of `X_r`.

## 5. Exact theorem-applicability obstruction

**Proposition 5.1 (fractional surrogate retains the deleted digit).** For every
`N>=2` and `m>=1`, the proposed `F_0^frac` in (3.3) is not a function of
`X^(0)=(X_1,...,X_(N+m-2))`. Therefore it is not an admissible coordinate-zero
surrogate in Definition 2, and the precommitted certificate cannot invoke
Theorem 1 at any depth in the declared range.

**Proof.** Fix every digit other than `X_0` equal to zero. Compare

```text
x=(0,0,...,0),                  y=(1,0,...,0).              (5.1)
```

These words have the same dropped-coordinate input `x^(0)=y^(0)`. At `x`, all
`N` blocks are the all-zero word, so

```text
F_m(N;x)=binom(N,2).                                      (5.2)
```

Coordinate zero belongs only to block `I_0`. For a pair `{0,j}`, `1<=j<N`,
the intervals `I_0=[0,m-1]` and `I_j=[j,j+m-1]` have union size `m+j` when
`j<m` and `2m` when `j>=m`. Write

```text
u_j=|I_0 union I_j|=m+min(j,m).                            (5.3)
```

Thus (3.2)--(3.3) give exactly

```text
F_0^frac(x)=binom(N,2)-sum_(j=1)^(N-1) 1/u_j.              (5.4)
```

At `y`, block `B_0^m` begins with digit one, while every `B_j^m`, `j>=1`,
begins with digit zero. Hence none of the `N-1` pairs `{0,j}` collides. Pairs
with both starts positive do not use coordinate zero and therefore have zero
fractional charge at zero. Consequently

```text
d_0(y)=0,
F_0^frac(y)=F_m(N;y)<=binom(N-1,2).                        (5.5)
```

Since `u_j>=m+1>=2`,

```text
F_0^frac(x)-F_0^frac(y)
 >=(N-1)-sum_(j=1)^(N-1)1/u_j
 >=(N-1)/2>0.                                             (5.6)
```

Therefore the same `x^(0)=y^(0)` produces two different proposed surrogate
values. No measurable function on the dropped-coordinate domain can equal
`F_0^frac` for both. This is the exact Definition 2 applicability obstruction.
QED.

The minimal instance is `N=2,m=1`: `F_0^frac(0,0)=1/2`, while
`F_0^frac(1,0)=0`. The argument (5.1)--(5.6), not this finite example, proves
the universal obstruction.

This obstruction is decisive only for certificate (3.2)--(3.3). It is not a
counterexample to the desired concentration inequality, not a lower tail, and
not evidence that every variance-sensitive or fractional method must pay
`m^3`.

## 6. Strict improvement test and logarithmic range

The agenda asks either for explicit `c>0,gamma<3` or a decisive obstruction.
T187 takes the obstruction branch. No constants `c,gamma` are asserted.
Proposition 5.1 holds for every `N>=2,m>=1`; in particular it holds uniformly
on the declared nonempty logarithmic-depth range

```text
N>=100,                   1<=m<=floor(log_10 N).           (6.1)
```

Thus the certificate fails before a parameter substitution into the upper-tail
formula, and before any issue concerning expectation margins, union bounds, or
the strict `gamma<3` comparison. Reporting a tail exponent from (3.4) while
ignoring the failed dropped-coordinate hypothesis would be invalid.

## 7. Complete prior-item nonduplication boundary

`PRIOR_COMPARISON.csv` has exactly one row for every required item T144--T154,
T159--T172, T177, and T183: 27 rows total. Verification levels are load-bearing.
Files under `notes/` are unverified proof sketches; their notes only argue the
listed fingerprints, and no conclusion from them is imported. T166 is the one
machine-checked comparator. Literature-pinned reports provide checked source
statements, but their new substitutions remain proof sketches unless otherwise
stated.

The nearest prior item is T183. Its note argues that deleting every collision
whose support contains coordinate `r` produces a genuine function of the other
digits and pays a support-multiplicity factor, yielding an `m^3` upper-tail
bound. T187 neither imports that deduction nor repeats the certificate. It
tests the distinct idea of retaining a fractional part of each `r`-incident
collision to reduce the decrement sum. Proposition 5.1 identifies why that
retention is illegal: the retained fraction still knows whether the collision
occurred, hence still knows `X_r`. This is a local supplied-corpus distinction,
not a global novelty claim.

The other potentially confusing word is “fractional” in T152/T154. Those notes
argue about fractional interval covers and coordinate-capacity duals in entropy
censuses. T187's weights are realized-collision allocations inside a proposed
product-space deletion surrogate. The theorem, object, and failure are all
different.

## 8. Finite falsification replay

From a directory containing only the delivered artifacts, run:

```text
python3 verify_t187.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The standard-library script authenticates the canonical statement and sole
source; checks the exact source locator anchors, source cap, and 27 comparison
rows; exhaustively verifies ordered/diagonal reconstruction, the allocation
identity (3.4), and failure of dropped-coordinate invariance for small decimal
instances; and checks all structural guardrails. These finite checks are an
`experiment` that can falsify formulas. They are not proof of Proposition 5.1,
the source theorem, or any universal concentration statement.

## 9. Separate unproved transfer toward T7 or T107

**PI-FRACTIONAL-DELETION-REPLACEMENT (UNPROVED TRANSFER REQUIREMENT; NOT
ASSERTED).** To transfer any repaired version of this route toward T7, one
would first need a separately proved deterministic or probabilistic
concentration principle for the actual decimal digits of pi that replaces
product-coordinate independence and supplies legal coordinate-deleted
surrogates or equivalent conditional-variance control uniformly over a named
increasing prefix sequence and all required depths. One would then need a
proved bridge from exact decimal-block equality to T7's required symbolic
collision interface with all endpoint and carry conventions. For a transfer
toward T107, an additional checked conversion would have to meet T107's literal
triangular Fourier and boundary budgets. None of these premises is supplied by
the iid obstruction or finite replay.

## 10. Fixed-pi claim firewall and sole endpoint

Every mathematical object tested here uses independent uniform random decimal
digits. The decimal digits of pi are not known to satisfy that premise. Exact
block equality is not the canonical strict circle-distance event.

There is no fixed-pi claim, no A1 claim, no C1 claim, and no C2 claim. No claim
about normality, Martin-Lof randomness, T7, or T107 for pi is made.

**SCOPED RELATED-MODEL VERDICT (1/1): CLOSE THIS CERTIFICATE.** The fixed
fractional support-deletion proposal (3.2)--(3.3) cannot improve T183's `m^3`
loss because it is not a coordinate-deleted surrogate under the sole pinned
theorem: Proposition 5.1 gives an exact obstruction for every `N>=2,m>=1`,
including the full declared logarithmic-depth range. This verdict concerns
only that iid related-model certificate, not the concentration law itself and
not any fixed-pi statement.
