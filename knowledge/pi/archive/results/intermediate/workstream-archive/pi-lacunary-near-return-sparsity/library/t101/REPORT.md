# T101: coherent successor splitting fails for regular paperfolding

Claim label: **proof sketch**.  The universal argument below is an elementary
derivation from the displayed definition of the regular paperfolding word.  It
does not use the T91, T94, or T97 notes as premises.  The accompanying replay
is an **experiment** which checks transcription over finite ranges; it is not
the proof of the universal statements.

This is an **A13 sibling** of the canonical fixed-pi question.  It makes no
claim about pi, C1, C2, canonical A1, normality, decimal factor complexity, or
digit occurrence.

## 1. Canonical scope and normalized sibling statement

The immutable canonical statement is vendored byte-for-byte as
`canonical_statement.txt`.  Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

That statement counts strict circle near returns of the fixed decimal orbit of
pi.  T101 changes the number, alphabet, predicate, and scale, so it is only the
recorded A13 sibling below.

For every positive integer `u`, write uniquely

```text
u = 2^a(2j+1),  a,j >= 0,
```

and define the one-based regular paperfolding word

```text
p_u = j mod 2.                                             (1.1)
```

For `s>=1` and `n>=0`, define the literal factor

```text
B(s,n) = p_s p_(s+1) ... p_(s+n-1).                       (1.2)
```

`B(s,0)` is the empty word.  For a binary word `w` of length `n` and a
full-prefix start cutoff `N>=1`, put

```text
c_N(w)   = #{s in {1,...,N}: B(s,n)=w},
c_N(wb)  = #{s in {1,...,N}: B(s,n+1)=wb},  b in {0,1}.
                                                                  (1.3)
```

Only the start is restricted.  A length-`n+1` child at start `N` may inspect
symbols after `p_N`.  Thus the inspected word is `p_1...p_(N+n)`, all factors
overlap as usual, and there is no terminal loss.  In particular,

```text
c_N(w)=c_N(w0)+c_N(w1).                                   (1.4)
```

The full-prefix collision energy is

```text
E(n,N) = sum_(w in {0,1}^n) c_N(w)^2
       = #{(s,t) in {1,...,N}^2:B(s,n)=B(t,n)}.            (1.5)
```

The second expression makes the literal convention explicit: pairs are
ordered, diagonal pairs are included, and overlaps are unrestricted.

Fix real `0<eta<=1/2`.  A parent `w` is `eta`-split at `(n,N)` when

```text
eta*c_N(w) <= c_N(w0)  and  eta*c_N(w) <= c_N(w1).         (1.6)
```

Let

```text
SplitEnergy(n,N,eta)
  = sum_(eta-split w of length n) c_N(w)^2.                (1.7)
```

For fixed `0<mu<1`, level `n` is `(mu,eta)`-splitting at cutoff `N` if

```text
mu*E(n,N) <= SplitEnergy(n,N,eta).                         (1.8)
```

The binary upper bound `eta<=1/2` replaces T14's decimal `eta<=1/10`; this
change is explicit and natural because there are exactly two successors.

### Dyadic triangular family

Declare once and for all

```text
N_K=2^K,  K>=0.                                            (1.9)
```

For `m>=0`, let

```text
SplitCount(m,K,mu,eta)
  = #{n in {0,...,m-1}: n is (mu,eta)-splitting at N_K}.   (1.10)
```

The complete paperfolding analogue of T14's coherent predicate asks whether
there exist fixed reals and integers

```text
0<mu<1,  0<eta<=1/2,  d>0,  B>=0,  m0,K0>=0              (1.11)
```

and, if one retains T14's measure clause, one weak limit `nu` of the empirical
shift-orbit measures

```text
nu_K = 2^(-K) sum_(s=1)^(2^K) delta_(shift^(s-1) p),       (1.12)
```

such that

```text
for every K>=K0 and every m with m0<=m<=K,
d*m-B <= SplitCount(m,K,mu,eta).                           (1.13)
```

All constants and the single dyadic prefix sequence are outside the
`K,m` triangle.  The obstruction below disproves (1.13), independently of
whether (1.12) has a weak limit.  No measure-theoretic premise is used.

## 2. Literal decimation and complete equality profiles

Removing one factor of two in (1.1), and evaluating odd indices directly,
gives

```text
p_(2a)=p_a       (a>=1),
p_(2a+1)=a mod 2 (a>=0).                                  (2.1)
```

Let `T(e,q)` be the alternating binary word of length `q` beginning in `e`,
and put

```text
h=ceil(n/2),  l=floor(n/2).                               (2.2)
```

Separating even and odd offsets in (1.2) gives, point by point,

```text
B(2a,n)   = interleave(B(a,h),   T(a mod 2,l)),
B(2a+1,n) = interleave(T(a mod 2,h), B(a+1,l)).            (2.3)
```

The interleave starts with its first argument.  The `a+1` in the second row is
an endpoint shift, not a fitted correction.

Write `Eq(s,t,n)` for `B(s,n)=B(t,n)` and `Alt(e,s,n)` for
`B(s,n)=T(e,n)`.  Define the exact guard

```text
altEq(c,d,q) := (q=0) or (c=d).                            (2.4)
```

Equality of two interleavings is equivalent to equality of both components.
Substitution of (2.3) therefore gives all four start-parity profiles:

```text
Eq(2a,2b,n)
 <=> Eq(a,b,h) and altEq(a mod 2,b mod 2,l),

Eq(2a+1,2b+1,n)
 <=> altEq(a mod 2,b mod 2,h) and Eq(a+1,b+1,l),

Eq(2a,2b+1,n)
 <=> Alt(b mod 2,a,h) and Alt(a mod 2,b+1,l),

Eq(2a+1,2b,n)
 <=> Alt(a mod 2,b,h) and Alt(b mod 2,a+1,l).              (2.5)
```

The legal domains are `a,b>=1` for an even start and `a,b>=0` for an odd
start.  These four iff rows are exhaustive; no implication is being reversed
without proof.

No factor of length four is alternating.  Any four consecutive positions
contain two odd positions `2a+1,2a+3`.  Their symbols are `a mod 2` and
`(a+1) mod 2`, hence differ, whereas symbols two places apart in an alternating
word agree.  Consequently

```text
Alt(e,s,n) is false for every e,s once n>=4.               (2.6)
```

If `n>=7`, then `h>=4`, so both mixed rows in (2.5) are impossible:

```text
Eq(s,t,n) implies s and t have the same parity, n>=7.      (2.7)
```

This is the only factor-profile vanishing used below.

## 3. Exact same-parity recurrence

Let `S(n,M)` count the ordered equal-factor pairs from (1.5) whose starts have
the same parity.  Put

```text
P0(M)=floor(M/2),  P1(M)=ceil(M/2),
R(M)=P0(M)^2+P1(M)^2.                                     (3.1)
```

Partitioning `1,...,M` into `2a` and `2b+1`, then applying the first two rows
of (2.5), gives the complete recurrence

```text
S(0,M)=R(M),
S(1,M)=E(1,P0(M))+R(P1(M)),
S(n,M)=S(h,P0(M))+S(l,P1(M))       for n>=2.              (3.2)
```

For `n>=2`, both alternating components in a same-parity comparison are
nonempty, so their equality guard is exactly equality of the relevant start
parities; this is what turns the two child counts back into `S`.  At `n=1`,
the zero-length component imposes no guard, which forces the displayed special
row.  Thus no zero-length condition is silently strengthened.

For `M=2^d`, let `z_d=#{s<=2^d:p_s=1}`.  The even starts contribute
`z_(d-1)`.  For `d>=2`, exactly half of the odd starts have `a mod 2=1`.
Starting from `z_1=0`, induction yields

```text
z_d=2^(d-1)-1,
E(1,2^d)=2^(2d-1)+2,
S(1,2^d)=4^(d-1)+2                 (d>=2).                (3.3)
```

The last identity adds `E(1,2^(d-1))` from the even starts and the two equal
odd-symbol classes, each of size `2^(d-2)`.

## 4. Solving the dyadic full-prefix recurrence

Fix integers

```text
K>=7,  7<=n<=K,
r=floor(log_2 n),  q=2^r,  q<=n<2q,
A=4^(K-r-2).                                               (4.1)
```

The exponent in `A` is nonnegative under these hypotheses.  By (2.7),
`E(n,2^K)=S(n,2^K)`.  Apply the `n>=2` row of (3.2) exactly `r` times.  Every
sample bound remains dyadic and becomes `2^(K-r)`.  The `2^r=q` resulting
lengths are either one or two: their sum is `n`, and repeated floor/ceiling
splitting keeps them within one of each other.  Hence there are

```text
X=2q-n  length-one nodes,
V=n-q   length-two nodes.                                  (4.2)
```

Split each length-two node once more.  This leaves `X` length-one nodes at
bound `2^(K-r)` and `Y=2V=2n-2q` length-one nodes at bound
`2^(K-r-1)`.  Formula (3.3) applies to both bounds.  Therefore

```text
E(n,2^K)
 = X(4^(K-r-1)+2)+Y(4^(K-r-2)+2)
 = (6q-2n)A+2n.                                           (4.3)
```

This is an exact ordered, diagonal-inclusive, all-first-start count.  It is
not a canonical-transversal count and contains every occurrence multiplicity.

The adjacent-depth drop also closes exactly.  If `n<2q-1`, use (4.3) with the
same `r`; if `n=2q-1`, use `r+1` for `n+1=2q`.  Both calculations give

```text
E(n,2^K)-E(n+1,2^K)=2(A-1)       (7<=n<K).                (4.4)
```

At the dyadic boundary, explicitly,

```text
E(2q-1,2^K)=(2q+2)A+4q-2,
E(2q,2^K)=2qA+4q,
```

so (4.4) does not assume scalar closure across a changed profile.

## 5. Successor energy identity and infinite obstruction

For every binary stream, not just paperfolding, (1.4) and grouping each child
under its unique parent give

```text
E(n,N)-E(n+1,N)
 = sum_w [(c_N(w0)+c_N(w1))^2-c_N(w0)^2-c_N(w1)^2]
 = 2 sum_w c_N(w0)c_N(w1).                                (5.1)
```

This is the load-bearing successor-count recurrence.  It is exact because the
same `N` starts occur in both rows.

An `eta`-split parent with `c_N(w)=0` contributes zero to (1.7) and may be
discarded.  For every remaining split parent write
`x=c_N(w0)/c_N(w)`.  Then `eta<=x<=1-eta`, and, since
`0<eta<=1/2`,

```text
c_N(w0)c_N(w1)=x(1-x)c_N(w)^2
              >= eta(1-eta)c_N(w)^2.                      (5.2)
```

Summing (5.2) only over split parents and using (5.1) yields

```text
2 eta(1-eta) SplitEnergy(n,N)
 <= E(n,N)-E(n+1,N).                                      (5.3)
```

Now take `N=2^K` and the triangle `7<=n<m<=K`.  Since
`6q-2n>=2q+2`, equations (4.3)--(4.4) imply

```text
SplitEnergy(n,2^K)/E(n,2^K)
 <= (A-1)/(eta(1-eta)((6q-2n)A+2n))
 < 1/(2q eta(1-eta))
 < 1/(n eta(1-eta)).                                      (5.4)
```

Consequently, if level `n` is `(mu,eta)`-splitting, then necessarily

```text
n < 1/(mu eta(1-eta)).                                    (5.5)
```

This is an exact infinite obstruction, not an asymptotic inference.  For fixed
admissible `mu,eta`, every triangle entry satisfies the explicit uniform bound

```text
SplitCount(m,K,mu,eta)
 <= 7 + ceil(1/(mu eta(1-eta))).                           (5.6)
```

The first seven levels `0,...,6` are deliberately charged without any claim
about them.  The remaining levels obey (5.5).

Suppose (1.13) held with fixed `d>0` and `B>=0`.  Choose an integer `K` above
`K0,m0`, the right side of (5.6), and `(B+right-side)/d`, and set `m=K`.
Then (1.13) says the splitting count is strictly larger than its uniform upper
bound (5.6), a contradiction.  Therefore:

```text
The regular-paperfolding dyadic full-prefix analogue of T14's coherent
positive-density successor-splitting predicate is false.                 (5.7)
```

This conclusion is independent of the weak-limit clause and independent of
every sketch-level premise in T91, T94, and T97.

## 6. Mechanism fingerprint

### Machine-checked T37/T49 comparison

The machine-checked T37/T49 modules concern one deliberately staged decimal
stream.  Their mechanism exhaustively repeats all seed words at each stage.
T49 has fixed witnesses `(mu,eta,d,B)=(1/2,1/20,1,0)` and every shallow level
in its triangle splits.  Its collision mass is spread over all successors by
construction even though T37 excludes one stable original-coordinate branch.

Paperfolding has the opposite fingerprint.  Its valuation rule gives exact
finite-state decimation, but (4.4) says the one-step collision loss is only
`2(A-1)` against row energy of order `nA`.  By (5.3), all quantitatively split
parents together therefore carry only `O(1/n)` of collision energy.  Finite
state synchronization is present, but positive-density energy splitting is
absent.  Thus T37/T49's exhaustive-stage synchronization, not merely low
description or finite-state recursion, is the load-bearing difference.

### Changed evidence from T91/T94/T97

The T91 note argues (unverified) that canonical paperfolding representatives
do not preserve full-prefix multiplicities.  T101 avoids that issue by using
the literal counts (1.3) throughout.

The T94 note argues (unverified) for a finite profile recurrence, and the T97
note argues (unverified) for diagonal collision asymptotics.  T101 does not
take either claim as a premise: Sections 2--4 re-derive the exact decimation,
same-parity recurrence, dyadic formula, and adjacent-depth drop.  The new
information is (5.3)--(5.7): collision asymptotics do not imply coherent
successor splitting, and in this model exact recurrence proves the opposite.

## 7. Pi-specific transfer hypothesis and exact kill tests

G19 concerns synchronization of T64's machine-checked one-row Fourier
criteria along one increasing prefix sequence for the actual decimal orbit of
pi.  Paperfolding can approach that goal only under an additional, explicitly
pi-specific hypothesis:

**Full-profile pi renormalization hypothesis (conjecture, not asserted).**  At
one fixed increasing sequence of pi cutoffs, the literal half-open decimal
parent and successor count trees, including every boundary and carry state,
admit a finite-state simultaneous renormalization of depth and cutoff.  The
state vector must preserve all starts, evaluate T64's collected circle-Fourier
remainder and active-boundary terms, and force a fixed positive fraction of
levels in every large triangle to have a fixed positive relative energy drop.

Paperfolding supplies none of the italicized pi-specific content.  Moreover,
copying only its scalar collision recurrence cannot work.  The smallest exact
closure test is

```text
E(2,3)=3,
E(ceil(2/2),floor(3/2))+E(floor(2/2),ceil(3/2))
  =E(1,1)+E(1,2)=1+4=5.                                  (7.1)
```

Indeed the three length-two factors at starts `1,2,3` are `00,01,10`, while
the first two length-one symbols are both zero.  Exhausting `M=0,1,2` first
shows that `(n,M)=(2,3)` is the smallest failure ordered by `n>=2` and then
`M`.  Thus any scalar paperfolding-to-pi transfer is killed before Fourier
estimation; a survivor must retain the parity and boundary profiles of
Section 2.

Even a full-profile copy would not provide G19's required coherent splitting.
For any proposed fixed `mu,eta`, choose an integer
`n>=max(7,1/(mu eta(1-eta)))` and then choose `K>n`.  Equations
(4.3)--(4.4), the successor estimate (5.3), and the algebra in (5.4) give
`SplitEnergy(n,2^K)/E(n,2^K)<mu`.  This is an exact recurrence kill at an
explicit admissible source depth.  Hence the paperfolding recurrence cannot be
transported as a positive-density splitting mechanism without adding a
genuinely stronger pi-specific input.

## 8. Replay

From a directory containing only the delivered artifacts, run

```text
python3 verify_t101.py
sha256sum -c SHA256SUMS
```

The verifier uses exact integer and rational arithmetic.  It checks the
canonical hash, literal decimation profiles, the same-parity recurrence, mixed
vanishing, (4.3), (4.4), the universal successor identity on finite rows, the
quantitative bound for several rational parameter pairs, and the minimal
scalar-closure failure.  These bounded checks are **experiment** only; the
universal proof sketch is Sections 2--5.

## 9. Verdict

**close.**

The exact infinite obstruction (5.5)--(5.7) closes regular paperfolding as a
source of T14-style coherent positive-density successor splitting on the
declared dyadic full-prefix triangles.  It does not affect pi or G19: those
would require the separate pi-specific full-profile and Fourier/boundary
hypothesis in Section 7.  The result is an A13 sibling only, with no pi, C1, or
C2 claim.
