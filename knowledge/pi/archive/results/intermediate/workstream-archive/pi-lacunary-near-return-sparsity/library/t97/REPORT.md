# T97: exact diagonal collisions for regular paperfolding

Claim label: **proof sketch**.  This note gives a complete symbolic derivation,
but no Lean formalization.  The accompanying finite replay is an `experiment`
that checks transcription only.  Every theorem in this note concerns the
regular paperfolding word defined below, not pi.

## 1. Scope and normalized statement

The immutable canonical pi question is vendored byte-for-byte as
`canonical_statement.txt`.  Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

That question concerns strict circle near returns of the fixed decimal orbit
of pi.  This note instead studies a sibling symbolic system.  For every
positive integer `m`, write uniquely

```text
m = 2^a (2j+1),  a,j >= 0,
```

and define the one-based regular paperfolding word by

```text
p_m = j mod 2.                                               (1.1)
```

For `s>=1` and `n>=0`, define the literal factor

```text
B(s,n) = p_s p_(s+1) ... p_(s+n-1).                         (1.2)
```

For `n,M>=0`, define

```text
C(n,M) = #{(s,t) in {1,...,M}^2 : B(s,n)=B(t,n)}.           (1.3)
```

Pairs in (1.3) are ordered, diagonal pairs are included, overlaps are allowed,
and `M` is the number of starts.  When `M,n>=1`, the required word is exactly
`p_1...p_(M+n-1)`.  When `n=0`, all factors are empty and `C(0,M)=M^2`; no
symbol is inspected.  The agenda's diagonal sequence means

```text
D_k = C(k,2^k),  k a positive integer tending to infinity. (1.4)
```

This fixes the possible ambiguities in indexing, endpoint, pair orientation,
diagonal inclusion, overlap, zero length, and the two distinct roles of `k`.

The derivation below starts from (1.1)--(1.3).  The earlier T94 note is an
unverified proof sketch and is not used as an established premise.

## 2. Result

For `k>=7`, put

```text
r = floor(log_2 k),             x_k = k/2^r in [1,2).       (2.1)
```

Then the exact diagonal collision count is

```text
C(k,2^k) = (3*2^(r+1)-2k) 4^(k-r-2) + 2k.                 (2.2)
```

Consequently

```text
k C(k,2^k)/4^k = x_k(3-x_k)/8 + 2k^2/4^k.                 (2.3)
```

In particular, for every `k>=7`, the explicit two-sided bounds

```text
1/4 + 2k^2/4^k <= k C(k,2^k)/4^k
                    <= 9/32 + 2k^2/4^k                    (2.4)
```

hold.  The normalization does not converge.  More exactly,

```text
liminf  k C(k,2^k)/4^k = 1/4,
limsup  k C(k,2^k)/4^k = 9/32,                             (2.5)
```

and its complete set of subsequential limits is `[1/4,9/32]`.

## 3. Literal decimation

Directly removing one factor of two in (1.1), or evaluating an odd index,
gives

```text
p_(2a)=p_a          (a>=1),
p_(2a+1)=a mod 2    (a>=0).                                (3.1)
```

Let `T(e,m)` be the alternating binary word of length `m` beginning with
`e`, and put

```text
h=ceil(n/2),       l=floor(n/2).                            (3.2)
```

Separating even and odd offsets in a factor gives

```text
B(2a,n)   = interleave(B(a,h),   T(a mod 2,l))   (a>=1),
B(2a+1,n) = interleave(T(a mod 2,h), B(a+1,l))   (a>=0).    (3.3)
```

The interleave begins with its first argument.  For example, the even-offset
symbols in the first row are `p_(2(a+u))=p_(a+u)`, while its odd-offset symbols
are `p_(2(a+u)+1)=(a+u) mod 2`.  This proves the first row pointwise; the
second is identical.  Thus endpoint shifts and component lengths in (3.3) are
not inferred from data.

## 4. Complete five-profile recurrence

Define the five profile types

```text
E(s,t,n) : B(s,n)=B(t,n),
A_e(s,n) : B(s,n)=T(e,n),              e in {0,1},
K_e(s,n) : B(s,n)=e^n,                 e in {0,1}.           (4.1)
```

Define the complete guards

```text
eta(c,d,m)   := (m=0) or (c=d),
gamma(c,d,m) := (m=0) or (m=1 and c=d).                     (4.2)
```

The first compares alternating words, and the second compares an alternating
word with a constant word.  Equality of interleavings is equivalent to
componentwise equality.  Substitution of (3.3) therefore gives the following
iff table.

For `a,b>=1` in the even-even row, `a,b>=0` in the odd-odd row, and the
corresponding mixed domains (`a>=1,b>=0` or `a>=0,b>=1`),

```text
E(2a,2b,n)
  <=> E(a,b,h) and eta(a mod 2,b mod 2,l),

E(2a+1,2b+1,n)
  <=> eta(a mod 2,b mod 2,h) and E(a+1,b+1,l),

E(2a,2b+1,n)
  <=> A_(b mod 2)(a,h) and A_(a mod 2)(b+1,l),

E(2a+1,2b,n)
  <=> A_(a mod 2)(b,h) and A_(b mod 2)(a+1,l).              (4.3)
```

For `a>=1` in each even row and `a>=0` in each odd row,

```text
A_e(2a,n)
  <=> K_e(a,h) and gamma(a mod 2,1-e,l),

A_e(2a+1,n)
  <=> gamma(a mod 2,e,h) and K_(1-e)(a+1,l),

K_e(2a,n)
  <=> K_e(a,h) and gamma(a mod 2,e,l),

K_e(2a+1,n)
  <=> gamma(a mod 2,e,h) and K_e(a+1,l).                   (4.4)
```

Here (4.3) has four start-parity rows.  Instantiating `e=0,1` in (4.4) gives
four A rows and four K rows.  These 12 rows exhaust every profile type,
profile parameter, and legal start parity.  At `n=0`, every predicate in
(4.1) is true because all involved words are empty.  This supplies the full
initial condition.

For termination at `n=1`, length alone is not a valid measure.  A formal
predicate evaluation can first define K by lexicographic induction on `(n,s)`,
then A from K, and then E from A and smaller E instances, using `(n,s+t)` for
E.  Every same-length call at `n=1` comes from a legal even-start row and
replaces `2a` by `a`, strictly decreasing the positive start.  Every odd-start
row calls a recursive predicate only at `l=0`, so its length decreases.
Equivalently, the count recurrence below has the simpler decreasing measure
`(n,M)`.

## 5. Multiplicity recurrence and initial conditions

Put

```text
P_0(M)=floor(M/2),        P_1(M)=ceil(M/2),
R(M)=P_0(M)^2+P_1(M)^2.                                  (5.1)
```

For `r,e in {0,1}`, let

```text
AA_(r,e)(n,M)=#{s:1<=s<=M, s mod 2=r and A_e(s,n)},
KK_(r,e)(n,M)=#{s:1<=s<=M, s mod 2=r and K_e(s,n)}.        (5.2)
```

Their complete bases are

```text
AA_(r,e)(0,M)=KK_(r,e)(0,M)=P_r(M),
AA_(r,e)(n,0)=KK_(r,e)(n,0)=0.                            (5.3)
```

For `n,M>0`, counting the iff rows (4.4) gives

```text
AA_(0,e)(n,M)
 = sum_(q=0,1) gamma(q,1-e,l) KK_(q,e)(h,P_0(M)),

AA_(1,e)(n,M)
 = sum_(q=0,1) gamma(q,e,h) KK_(1-q,1-e)(l,P_1(M)),

KK_(0,e)(n,M)
 = sum_(q=0,1) gamma(q,e,l) KK_(q,e)(h,P_0(M)),

KK_(1,e)(n,M)
 = sum_(q=0,1) gamma(q,e,h) KK_(1-q,e)(l,P_1(M)).          (5.4)
```

The `1-q` terms are forced by the odd-start bijection.  Namely, writing an odd
start as `2b+1` and setting `u=b+1` maps it bijectively to
`1<=u<=P_1(M)`, with

```text
b mod 2 = 1-(u mod 2).                                    (5.5)
```

For completeness, let `z(M)=#{s:1<=s<=M, p_s=1}`.  Then

```text
z(0)=0,
z(M)=z(P_0(M))+floor(P_1(M)/2),
C(1,M)=z(M)^2+(M-z(M))^2.                                 (5.6)
```

Let S count equal-factor pairs with starts of the same parity, and H count
equal-factor pairs oriented from an even start to an odd start.  Their bases
and recurrences are

```text
S(n,0)=H(n,0)=0,
S(0,M)=R(M),
S(1,M)=C(1,P_0(M))+R(P_1(M)),
S(n,M)=S(h,P_0(M))+S(l,P_1(M))                 (n>=2),     (5.7)

H(n,M)=sum_(r,q in {0,1})
  AA_(r,1-q)(h,P_0(M)) AA_(q,r)(l,P_1(M)),                 (5.8)

C(0,M)=M^2,
C(n,M)=S(n,M)+2H(n,M)                         (n>=1).      (5.9)
```

The special `n=1` row in (5.7) is necessary because a zero-length alternating
component imposes no parity guard.  Formula (5.8) follows from the mixed E row
and (5.5).  Reversing an ordered mixed pair is a bijection, so the opposite
orientation also has cardinality H.  Same-parity, even-to-odd, and odd-to-even
pairs are disjoint and exhaustive, proving (5.9).  In particular, (5.9)
retains every occurrence multiplicity, including all diagonal pairs.

For computation, define `z`, then K, A, S, H, and C in that dependency order.
In every self-call at `n>=2`, length decreases.  At `n=1`, every possible
self-call has bound `P_0(M)<M` for `M>0`; (5.3) handles `M=0`.  Thus
lexicographic induction on `(n,M)` proves termination and literal semantics of
(5.3)--(5.9).  This is the recurrence proof; finite checks are not used here.

## 6. Vanishing of mixed collisions

No paperfolding factor of length four is alternating.  Indeed, any four
consecutive absolute positions contain two odd positions at distance two,
say `2a+1` and `2a+3`.  By (3.1), their symbols are respectively `a mod 2`
and `(a+1) mod 2`, hence differ.  Symbols at distance two in an alternating
word are equal, a contradiction.  Therefore

```text
A_e(s,n) is false for every s,e when n>=4.                 (6.1)
```

In each mixed row of (4.3), one A factor has length `h=ceil(n/2)`.  If `n>=7`,
then `h>=4`, so that factor is false.  Hence

```text
H(n,M)=0 and C(n,M)=S(n,M) for every n>=7 and M>=0.        (6.2)
```

## 7. Exact dyadic boundary value

Let

```text
z_d=#{1<=s<=2^d:p_s=1}.
```

The even positions contribute `z_(d-1)`.  For `d>=2`, the odd positions are
`2a+1`, `0<=a<2^(d-1)`, and exactly `2^(d-2)` of these have `a mod 2=1`.
Since `z_1=0`, induction gives

```text
z_d=2^(d-1)-1                    (d>=1),
C(1,2^d)=2^(2d-1)+2              (d>=1).                  (7.1)
```

For `d>=2`, the even starts in `S(1,2^d)` contribute
`C(1,2^(d-1))=2^(2d-3)+2`.  Among the `2^(d-1)` odd starts, each symbol occurs
`2^(d-2)` times, so they contribute `2*2^(2d-4)=2^(2d-3)` ordered pairs.
Thus

```text
S(1,2^d)=4^(d-1)+2                         (d>=2).         (7.2)
```

## 8. Solving the diagonal recurrence

Fix `k>=7` and let `r=floor(log_2 k)`, so `2^r<=k<2^(r+1)`.
By (6.2), begin with `C(k,2^k)=S(k,2^k)`.  Apply the `n>=2` row of (5.7)
exactly r times.  Because every bound is a power of two, both children at
depth d have bound exactly `2^(k-d)`.

At depth r there are `2^r` length arguments.  Repeated use of
`ceil(n/2)+floor(n/2)=n` shows that their sum is k, while balanced splitting
shows that they differ by at most one.  Their average is in `[1,2)`, so every
length is 1 or 2.  If X and V are the numbers of length-one and length-two
nodes, then

```text
X+V=2^r,        X+2V=k,
X=2^(r+1)-k,    V=k-2^r.                                  (8.1)
```

Split each length-two node once more.  This produces

```text
X=2^(r+1)-k
```

length-one leaves at depth r and

```text
Y=2V=2k-2^(r+1)
```

length-one leaves at depth `r+1`.  Their bounds are respectively
`2^(k-r)` and `2^(k-r-1)`.  For `k>=7`, the smaller exponent is at least 4,
so (7.2) applies.  Therefore

```text
C(k,2^k)
 = X(4^(k-r-1)+2) + Y(4^(k-r-2)+2)
 = (3*2^(r+1)-2k)4^(k-r-2)+2k.                            (8.2)
```

This proves (2.2) symbolically from the literal recurrence and its initial
conditions.

## 9. Asymptotics and exact cluster set

Substitute `k=x_k 2^r` into (8.2) and divide by `4^k/k`.  Exact cancellation
gives (2.3):

```text
k C(k,2^k)/4^k = f(x_k)+2k^2/4^k,
f(x)=x(3-x)/8=9/32-(x-3/2)^2/8.                           (9.1)
```

On `[1,2]`, the minimum of f is `1/4` and its maximum is `9/32`.  This proves
the explicit bounds (2.4), and the correction `2k^2/4^k` tends to zero.

Along `k=2^m`, the mantissa is 1, so (9.1) tends to `1/4`.  Along
`k=3*2^(m-1)`, the mantissa is `3/2`, so it tends to `9/32`.  Thus the sequence
does not converge and (2.5) holds.

For the full cluster set, fix any `x in [1,2)` and take
`k_m=floor(x 2^m)`.  Then eventually `floor(log_2 k_m)=m` and the dyadic
mantissa tends to x, so (9.1) tends to f(x).  Conversely, every sequence of
mantissas in `[1,2)` has a subsequence converging in `[1,2]`, and (9.1) forces
the corresponding normalized collisions to tend to f of that limit.  Since
`f([1,2])=[1/4,9/32]`, there are no other subsequential limits.

## 10. Self-contained replay

From a directory containing only the delivered files, run

```text
python3 verify_t97.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical hash; the exact 12-row profile-state
inventory; every literal profile iff over a declared finite range; every
profile multiplicity and collision recurrence against direct factor counts;
the no-alternating-length-four lemma over a sanity range; the balanced-tree
leaf inventory; and (8.2) against the independently evaluated S recurrence for
`7<=k<=256`.  These are finite `experiment` checks.  The universal proof is
Sections 3--9.

## 11. Separate unproved pi transfer hypothesis

**Bounded-state collision-renormalization hypothesis for pi (conjecture).**
A comparable route for pi would require a finite, literally interpreted state
system for two decimal-orbit prefixes that is closed under simultaneous
renormalization of factor length and sample bound, retains all ordered
diagonal-inclusive multiplicities and decimal carry/boundary states, and has a
proved dominant matrix or renewal decomposition strong enough to control its
collision normalization uniformly across the required scales.  To address
the canonical metric statistic, it would additionally need a proved map from
strict circle near returns to those exact states with all boundary errors
quantified.

No such system is proved here.  Regular paperfolding decimation (3.1) is the
special input that makes the five profiles close; it has not been established
for pi.  Accordingly, this note makes no T14, T64, C1, C2, fixed-pi,
normality, decimal-factor-complexity, or digit-occurrence claim.

## 12. Conclusion

The literal regular-paperfolding factor definitions yield a complete
five-profile recurrence with explicit domains and initial conditions.  On the
diagonal `M=2^k`, mixed parity disappears for `k>=7`, and the balanced
recurrence tree gives the exact formula (2.2).  The normalized count oscillates
with the dyadic mantissa of k: its liminf is `1/4`, its limsup is `9/32`, and
its exact cluster set is the interval between them.  This is a result only for
regular paperfolding and does not use T94's sketch as an established premise.
