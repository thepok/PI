# T90: fixed-point expanding-map models

Search date: 2026-08-09 UTC.

Claim labels: `literature-checked` for the bounded five-source corpus in
`SOURCE_PINS.md`; `proof sketch` for the elementary discrepancy transfers in
Sections 3--6. No theorem about `Real.pi` is claimed.

## 1. Immutable question and normalized scope

The byte-exact canonical statement is delivered as `canonical_statement.txt`.
Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For real `x` and integers `n,N >= 1`, write

```text
Q_x(n,N) = #{(i,j) in {0,...,N-1}^2 :
               ||(10^i-10^j)x||_(R/Z) < 10^(-n)}.
```

The pairs are ordered, all `N` diagonal pairs are included, the inequality is
strict, and the distance is circular. The canonical fixed-pi assertion is

```text
for every integer A >= 1
  there exists an integer n0 >= 1
    such that for every integer n >= n0
      there exists an integer N >= 1
        with A*n*Q_pi(n,N) <= N^2.
```

This report neither changes that quantifier order nor substitutes a generic,
almost-everywhere, invariant-measure, normal-number, base-2, off-diagonal, or
pair-correlation assertion for it.

### Quantifier and normalization ambiguities resolved

1. A discrepancy estimate `D_N = O(f(N))` is read literally as existence of
   constants `C > 0` and `N1 >= 1`, depending only on the fixed point and the
   fixed base, such that `D_N <= C*f(N)` for every `N >= N1`.
2. Source orbits indexed by `j >= 1` are not silently identified with the
   canonical orbit indexed by `j >= 0`; the one-point replacement is displayed
   in Section 3.
3. Stoneham's theorem is in base 2. Its statistic is always marked as a sibling
   under canonical ambiguity A13.
4. Poissonian pair correlation is off-diagonal and has threshold `s/N`.
   Diagonal restoration and its relation to a dyadic `Q` scale are displayed in
   Section 6.
5. A failure of PPC does not imply failure of the weak existential near-return
   estimate. The Stoneham candidate exhibits both normality and non-PPC.
6. The search is bounded by the declared queries and stopping rule in
   `SEARCH_LOG.md`; it is not a claim that no other fixed-point theorem exists.

## 2. Retained corpus and candidates

Exactly three fixed candidates and five primary sources are retained. Four
sources establish candidate behavior; Becher--Graus is retained only as the
current-status source for normality of `pi`.

| ID | Fixed candidate | Map and proved behavior | Primary sources |
|---|---|---|---|
| L | Levin--Becher--Carton nested-necklace point `x_L,10` | `x -> 10x mod 1`; discrepancy `O((log N)^2/N)` | Becher--Carton |
| S | Scheerer's computable absolutely normal point `xi` | `x -> 10x mod 1`; discrepancy `O(log log N/log N)` from an explicit exponential-sum minimization | Scheerer |
| T | Stoneham point `alpha_(2,3) = sum_(m>=1) 1/(3^m 2^(3^m))` | `x -> 2x mod 1`; base-2 normal, but its orbit is not Poissonian | Stoneham; Larcher--Stockinger |

Becher--Graus (2026), source S5, is not a fourth candidate. Its introduction
states that `pi`, `e`, and `sqrt(2)` have not been proved normal in any base.

No almost-everywhere point is retained as a candidate. The local T3 audit is
used only as a comparison standard for generic metric work.

## 3. A common ordered, diagonal-inclusive transfer

This section is an elementary `proof sketch`, included so every candidate has
a literal translation rather than an appeal to the word "normal".

Let `y_0,...,y_(N-1)` be circle points and let

```text
D_N(y) = sup_I |#{j<N : y_j in I}/N - length(I)|,
```

where `I` ranges over intervals in `[0,1)`. For `0 < rho <= 1/2`, define the
ordered, diagonal-inclusive count

```text
Q_y(rho,N) = #{(i,j) in {0,...,N-1}^2 : ||y_i-y_j|| < rho}.
```

For fixed `i`, the circular ball of radius `rho` around `y_i` is one interval
or the union of two intervals, of total length `2*rho`. Enlarging open
endpoints by an arbitrarily small amount handles every boundary convention.
The discrepancy definition therefore gives

```text
#{j<N : ||y_i-y_j|| < rho} <= N*(2*rho + 2*D_N(y)).
```

Summing over all `i` gives the transfer lemma

```text
Q_y(rho,N) <= N^2*(2*rho + 2*D_N(y)).                 (3.1)
```

The diagonal is already present in (3.1); it is not added afterward.

For a source orbit `({10^j x})_(j>=1)`, let `D_N^(1)(x)` be its discrepancy,
and let `D_N^(0)(x)` be the discrepancy of the canonical zero-based window
`j=0,...,N-1`. The two windows replace exactly one point, so for every interval

```text
|#{0<=j<N : {10^j x} in I} - #{1<=j<=N : {10^j x} in I}| <= 1,
```

and hence

```text
D_N^(0)(x) <= D_N^(1)(x) + 1/N.                      (3.2)
```

Taking `rho=10^(-n)` in (3.1) gives the exact source-to-sibling bridge

```text
Q_x(n,N)/N^2 <= 2*10^(-n) + 2*D_N^(0)(x).            (3.3)
```

Equations (3.1)--(3.3) retain strict circle distance, order, diagonal, and the
zero-based orbit.

## 4. Candidate L: nested-necklace point

### Literal source theorem

Becher--Carton, Theorem 1, states the following for each integer base `b`.
Levin's point constructed with the Pascal triangle matrix modulo 2 has a
base-`b` expansion obtained by concatenating `(m,m)`-nested perfect necklaces
for `m=2^d`, `d=0,1,2,...`. Conversely, every point `x` whose base-`b`
expansion has that concatenation satisfies

```text
there exist C>0 and N1>=1 such that for every N>=N1,
  D_N(({b^j x})_(j>=1)) <= C*(log N)^2/N.             (4.1)
```

The big-O quantifiers in (4.1) are the paper's convention. The source locators
are preprint p. 1 for discrepancy and normality, and Theorem 1 on p. 2.

Set `b=10` and name one such constructed point `x_L,10`. This is a fixed,
deterministically constructed point; no null exceptional set occurs.

### Literal `Q_x` translation

By (3.2)--(3.3), for all sufficiently large `N`,

```text
Q_(x_L,10)(n,N)/N^2
  <= 2*10^(-n) + 2*(C*(log N)^2/N + 1/N).             (4.2)
```

For each fixed integer `A>=1`, take the prescribed witness `N=10^n`. Then

```text
A*n*Q_(x_L,10)(n,10^n)/10^(2n)
 <= 2*A*n*10^(-n)
    + 2*A*n*(C*(n*log 10)^2+1)/10^n,
```

which tends to zero. Thus the source theorem plus (3.1)--(3.3) gives exactly

```text
for every integer A>=1 there exists n0>=1 such that
  for every integer n>=n0, with N=10^n,
    A*n*Q_(x_L,10)(n,N) <= N^2.                      (4.3)
```

This is a solved fixed-point sibling with a stronger prescribed witness. It
does not concern `pi`.

### Smallest transfer killer

The theorem's fixed-point premise is the explicit nested-necklace
concatenation. Substituting `pi` for `x_L,10` deletes that premise. No source in
the corpus proves that the decimal expansion of `pi` is such a concatenation,
or even that `D_N^(0)(pi) -> 0`. The first failed T3 discriminator is therefore
`P` (the named point), not scale, diagonal, or quantifier bookkeeping.

## 5. Candidate S: Scheerer's computable point

### Literal source theorem and construction

Scheerer defines `xi_0=0`. At step `m`, a finite set `sigma_m(xi_(m-1))` is
formed and `xi_m` is the smallest element minimizing the explicit nonnegative
finite exponential-sum functional

```text
A'_m(x) = sum_{-m<=t<=m, t!=0}
          sum_{i<=m, m0(r_i)<=m}
          |sum_{j=h_(m;r_i)+1}^{h_(m+1;r_i)} e(r_i^j*t*x)|^2.   (5.1)
```

The limit `xi` is absolutely normal. Theorem 2.4 states, for every fixed
integer base `r>=2`,

```text
there exist C_r>0 and N1(r)>=1 such that for every N>=N1(r),
  D_N(({r^j xi})_(j>=1)) <= C_r*log(log N)/log N.      (5.2)
```

The source locators are pp. 3--4 for (5.1) and the minimizer, pp. 4--5 for the
limit and absolute normality, and Theorem 2.4 on pp. 5--7 for (5.2).

### Literal `Q_x` translation

Set `r=10`. By (3.2)--(3.3), for all sufficiently large `N`,

```text
Q_xi(n,N)/N^2
 <= 2*10^(-n) + 2*(C_10*log(log N)/log N + 1/N).       (5.3)
```

For each fixed integer `A>=1`, take `N=10^(n^2)`. Then the discrepancy
contribution after multiplication by `A*n` is

```text
O_A(n*log(n^2*log 10)/(n^2*log 10)) = O_A(log n/n),
```

and the radius and `1/N` terms also tend to zero. Consequently

```text
for every integer A>=1 there exists n0>=1 such that
  for every integer n>=n0, with N=10^(n^2),
    A*n*Q_xi(n,N) <= N^2.                              (5.4)
```

Again this is a fixed constructed sibling, not a statement about `pi`.

### Smallest transfer killer and T10-shaped mismatch

The cancellation estimate used by Scheerer is obtained because each `xi_m`
is selected to minimize (5.1) over `sigma_m(xi_(m-1))`. The number `pi` is not
selected by that recursion. Replacing `xi` by `pi` therefore removes the
minimization inequality before any discrepancy conclusion is available.

Moreover, (5.1) is not T10's adaptive lag sum. T10's checked obstruction uses

```text
sum_{j<N-r} e(h*(10^r-1)*10^j*pi)
```

with moving `r`, `h<=256*A*n`, and every requested lag-orbit length. The source
does not bound that family at `pi`. Thus the first failure is again T3's `P`
discriminator, and the first quantitative T10 failure is the absent
point-specific minimizing bound for the adaptive coefficient
`h*(10^r-1)`.

## 6. Candidate T: Stoneham's fixed base-2 separator

### Literal source theorems

Stoneham defines, for an odd prime `p` and a primitive root `g modulo p^2`,

```text
w(g,p) = sum_(m>=1) 1/(p^m*g^(p^m)).                   (6.1)
```

On journal p. 372, immediately below equation (1.0), the paper states that
`w(g,p)` is a transcendental non-Liouville normal number. Taking `g=2,p=3` is
legal because 2 is a primitive root modulo 9, and (6.1) is exactly

```text
alpha_(2,3) = sum_(m>=1) 1/(3^m*2^(3^m)).              (6.2)
```

Larcher--Stockinger, Theorem 3, states literally that

```text
the sequence ({2^j*alpha_(2,3)})_(j in N)
does not have Poissonian pair correlations.             (6.3)
```

Their definition of PPC is

```text
for every real s>=0,
  lim_(N->infinity) (1/N) *
    #{1<=l!=m<=N : ||2^l*alpha_(2,3)-2^m*alpha_(2,3)|| <= s/N}
  = 2*s.                                                  (6.4)
```

Theorem 3 is on preprint p. 4. Its proof on pp. 14--16 takes `s=1` and
`N=2^w` and analyzes the repeated rational-period residues; it allows only
`O(log N)` exceptional close pairs outside the repeated-residue classes.

### Ordered, diagonal-inclusive translations

First define the zero-based strict base-2 sibling

```text
Q^(2)_alpha(n,N) = #{(i,j) in {0,...,N-1}^2 :
                         ||(2^i-2^j)*alpha|| < 2^(-n)}.      (6.5)
```

Stoneham normality means the discrepancy of the zero-based base-2 orbit tends
to zero. Applying (3.1) with base 2 shows, with every quantifier displayed,

```text
for every integer A>=1 there exists n0>=1 such that
  for every integer n>=n0 there exists N>=1 with
    A*n*Q^(2)_(alpha_(2,3))(n,N) <= N^2.                    (6.6)
```

Indeed choose `n0` so that `2*A*n*2^(-n)<=1/2` thereafter;
for each such `n`, then choose `N` so large that
`2*A*n*D_N<=1/2`. This is A13 sibling evidence only.

For exact diagonal restoration of (6.4), define

```text
R_alpha(s,N) = #{(l,m) in {1,...,N}^2 :
                       ||(2^l-2^m)*alpha|| <= s/N}.          (6.7)
```

Then, with no asymptotic error,

```text
R_alpha(s,N)/N
  = 1 + (1/N)*#{1<=l!=m<=N : ||(2^l-2^m)*alpha|| <= s/N}.   (6.8)
```

Thus (6.3)--(6.4) are exactly the displayed failure

```text
not [for every real s>=0, lim_(N->infinity) R_alpha(s,N)/N = 1+2*s].  (6.9)
```

At the proof's values `s=1,N=2^w`, (6.7) is the ordered,
diagonal-inclusive, positive-index dyadic `Q` statistic at radius `2^(-w)`.
The weak estimate (6.6) and the PPC failure (6.9) coexist. Therefore full PPC
is not necessary for the weak near-return target, even for one named normal
expanding-map orbit.

### Smallest transfer killers

1. `P`: `alpha_(2,3)` is not `pi`; Stoneham's rational-period construction is
   the fixed-point certificate.
2. `O`: the map is multiplication by 2, not multiplication by 10. Canonical
   ambiguity A13 requires a transfer, and no source supplies one.
3. `Q`: non-PPC is a failure of a universal limit in `N`; canonical A1 only
   asks for one `N` at each sufficiently large `n`. Equation (6.6) proves that
   this quantifier difference is substantive.

## 7. T3 discriminator matrix

Cells state what the source plus the displayed elementary transfer supplies
for its own fixed candidate. `NO FOR PI` is an applicability failure, not a
claim that the corresponding pi property is false.

| Candidate | P: named pi | O: zero-based base 10 | D: sharp two-index count | S: canonical scale | C: ordered + diagonal | Q: full weak quantifiers | First failure for pi |
|---|---|---|---|---|---|---|---|
| L | NO FOR PI; fixed `x_L,10` only | YES via (3.2) | YES via (3.1) | YES, `10^-n` | YES in (3.1) | YES for `x_L,10`, even `N=10^n` | P |
| S | NO FOR PI; fixed `xi` only | YES via (3.2) | YES via (3.1) | YES, `10^-n` | YES in (3.1) | YES for `xi`, even `N=10^(n^2)` | P |
| T | NO FOR PI; fixed `alpha_(2,3)` only | NO, base 2 | YES for (6.5), and PPC frontier (6.7) | NO, `2^-n` sibling | YES in (6.5),(6.7) | YES only for base-2 sibling (6.6) | P, then O |

No candidate fails because of diagonal restoration or the `forall A, exists
n0, forall n, exists N` bookkeeping. Every candidate fails to transfer at the
fixed point itself.

## 8. Accepted local interfaces and obstruction memory

The following statuses are part of the audit. Only machine-checked interfaces
are used as established formal facts.

| Local item | Verification used | Exact comparison |
|---|---|---|
| T2 | machine-checked | Normality of an explicit base-10 decimal orbit implies the ordered, diagonal-inclusive weak `Q_x` estimate. Candidates L and S instantiate the same sufficient mechanism, but (3.1) preserves their quantitative rates and prescribed `N`. T2 already contains Champernowne, so Champernowne was not retained as a new candidate. |
| T3 | literature-checked for its frozen six-source corpus | Supplies the ordered `P,O,D,S,C,Q` discriminator order. Its metric PPC and shrinking-target theorems are almost-everywhere and do not certify `pi`; the three retained candidates are fixed constructions instead. |
| T7 | machine-checked | Gives the pi-specific factor-three comparison between ordered metric near returns and half-open decimal cylinder collisions, and an exact finite-energy frontier. Candidate discrepancy proves its own metric bound directly; no candidate source supplies T7 collision decay for `pi`. |
| T10 | machine-checked necessary obstruction | Literal failure of canonical A1 forces adaptive low-harmonic lag resonances. Candidate S uses finite exponential sums, but only at its recursively minimized `xi`; none of the sources excludes T10's moving `(r,h,K)` family at `pi`. |
| T60 | unverified `proof sketch` note | The note argues that invariant Fourier identities and fixed-frequency Weyl cancellation do not yield adaptive moving-shell decay, and that Walsh and circle coefficients are not coefficientwise identical because of carries. These claims are cautionary only and are not premises of any transfer above. |
| T67 | machine-checked finite/conditional interface | Formalizes the empirical multiplier-ten endpoint defect, a qualified UPRID-to-T61 threshold implication, and the exact aggregate Walsh/cylinder-energy identity. It proves no fixed-pi cancellation. None of L, S, or T supplies its moving labeled-shell premise for `pi`. |
| T72 | unverified `proof sketch` random sibling | The note studies one common random multiplier and reports failure of a predetermined exact-form top-shell schedule. It is neither a theorem about the retained fixed points nor evidence about `pi`, and no conclusion here depends on it. |
| semantic obstruction memory | audit ledger, not a theorem | Retains the rules that genericity is not point membership, invariant identities are not decay, regrouping is not cancellation, abstract arrays are not orbit witnesses, and random behavior is not fixed-pi evidence. |

### Generic metric and invariant-measure distinction

The retained source theorems assert conclusions for specifically constructed
points. This is logically different from the T3 sources' conclusions for
Lebesgue-almost every multiplier: a full-measure set does not certify that
`pi` belongs to it. It is also stronger than merely taking an invariant weak
limit. Invariance under multiplication by 10 only identifies Fourier
coefficients along decimal rays; it does not make them vanish. The present
positive translations use pointwise discrepancy theorems, not invariance.

## 9. Exact property still unknown for pi

The common sufficient property isolated by candidates L and S is

```text
lim_(N->infinity) D_N(({10^j*pi})_(j=0,...,N-1)) = 0.        (9.1)
```

Equation (9.1) is equidistribution of the decimal multiplication orbit,
equivalently base-10 normality of `pi`. Becher--Graus, published in 2026,
states that `pi` has not been proved normal in any base. Therefore no rate
comparable to either `(log N)^2/N` or `log log N/log N` is available from a
proved normality theorem for `pi`.

Canonical A1 is syntactically weaker than (9.1), but the checked local
T2/T7/T10 interfaces do not prove a nonimplication; none is asserted here. The
unverified T60 note argues for related sibling separators, and that argument is
not a premise of this report. No retained source or checked local interface
supplies fixed-pi PPC or the adaptive T10/T67 moving-frequency cancellation.
The Stoneham candidate shows at a fixed base-2 orbit why replacing the weak
near-return target by PPC would over-strengthen that sibling goal.

## 10. Source and replay boundary

`SOURCE_PINS.md` gives DOI, URL, hash, theorem locator, and exact role for all
five sources. `SEARCH_LOG.md` records the dated search and stopping rule.
`verify_note.py` checks the source hashes, canonical hash, candidate/source
caps, authenticated theorem markers in the text derivatives, required local
comparisons, and the unique terminal classifications. It does not certify the literature
as exhaustive or promote the elementary transfers to machine-checked status.

## 11. Final classifications

| Candidate | Verdict |
|---|---|
| L: Levin--Becher--Carton nested-necklace point | hold as model |
| S: Scheerer computable absolutely normal point | close |
| T: Stoneham `alpha_(2,3)` | hold as model |
