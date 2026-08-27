# T94: finite paperfolding tensor-square collision recurrence

Claim label: **proof sketch**.  The recurrence and its induction are given in
full below and the finite transcription checks are replayable, but there is no
Lean formalization.  Every conclusion is scoped to the regular paperfolding
word.  Nothing here proves a statement about pi.

## 1. Scope, normalized statement, and ambiguities

The immutable canonical pi question is vendored as `canonical_statement.txt`.
Its verified SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

That question counts strict circle near returns of the fixed orbit of pi.  T94
instead treats the sibling model specified in the agenda.  Define the one-based
regular paperfolding word `p` by

```text
m = 2^a(2j+1),  a,j >= 0,       p_m = j mod 2.             (1.1)
```

For `s>=1`, `n>=0`, put

```text
B(s,n) = p_s p_(s+1) ... p_(s+n-1).                        (1.2)
```

For the actual statistic take `n>=1`, `M>=0` and

```text
C(n,M) = #{(s,t) in {1,...,M}^2 : B(s,n)=B(t,n)}.          (1.3)
```

Thus the inspected finite word is exactly `p_1...p_(M+n-1)` when `M>0`.
Pairs are ordered, the diagonal is included, and overlaps are allowed without
restriction.  If a reader instead calls the containing-word length `P`, then
`M=P-n+1`; T94 never silently interchanges these two parameters.  Length zero
is used only as the recurrence base, where `C(0,M)=M^2`.

The agenda leaves "declared full prefixes" open.  Equations (1.2)--(1.3) are
the chosen convention.  The source convention, endpoints, order, diagonal,
overlap, and zero-length auxiliary case are therefore explicit.

## 2. Symbol automaton and tensor square

Read the binary expansion of a positive integer from least significant bit to
most significant bit and then append two zero flush bits.  The complete DFAO
has states

```text
Q = {Z,A,O0,O1}, initial state Z, output 1 exactly at O1,

          input 0   input 1
Z            Z         A
A           O0        O1
O0          O0        O0
O1          O1        O1.                                  (2.1)
```

`Z` means that no `1` has yet appeared.  `A` means that the least significant
`1` was the last bit read.  The next bit is the low bit of
`(oddpart(m)-1)/2`; after that, `O0` or `O1` retains it.  Therefore the output
is exactly (1.1).  This is also proved directly by the induction in Section 5.

The literal symbol tensor square has the 16 ordered states `Q x Q`, alphabet
`{0,1} x {0,1}`, componentwise transition, and accepting-output predicate
"the two component outputs agree."  All `16*4=64` transitions exist and are
expanded and checked by `verify_recurrence.py`.

### 2.1 Finite factor-pair automaton

The symbol square alone compares one pair of symbols.  The following finite
extension recognizes and counts entire equal factors.

For low-bit comparison define

```text
High(d,x,y) = -1 if x<y,  +1 if x>y,  d if x=y.            (2.2)
```

After a more significant bit is read, that bit decides the comparison when it
differs; otherwise the lower-bit comparison `d` remains.  Let

```text
D={-1,0,+1},   Carry={0,1},
PB = D x Carry x Carry x Q x Q.                            (2.3)
```

Thus `PB` has `3*2*2*4*4=192` primitive states.  A state is
`(d,c_i,c_j,x_i,x_j)`.  On current bits
`a=n_bit`, `u=i_bit`, `v=j_bit`, `w=k_bit`, put

```text
r_i=u+w+c_i,   r_j=v+w+c_j,

delta_B((d,c_i,c_j,x_i,x_j);a,u,v,w)
 = (High(d,w,a), floor(r_i/2), floor(r_j/2),
    delta_Q(x_i,r_i mod 2), delta_Q(x_j,r_j mod 2)).        (2.4)
```

The initial primitive state is `(0,0,0,Z,Z)`.  After all input bits, apply
(2.4) twice with zero bits.  The first step flushes addition carries and the
second resolves a possible `A` symbol state.  A flushed state is bad exactly
when

```text
d=-1 and the two Q outputs differ.                          (2.5)
```

This says `k<n` and `p_(i+k) != p_(j+k)`.

Existentially project `k` by subset determinization.  For `S subset PB`, set

```text
D_(a,u,v)(S)={delta_B(q;a,u,v,w):q in S, w in {0,1}}.      (2.6)
```

Factor equality says that `S` contains no bad state.  Add two comparisons with
the public bound `M` and two seen-one flags for positivity.  The complete outer
state universe is

```text
O = Powerset(PB) x D x D x {0,1} x {0,1},
|O| = 36*2^192.                                            (2.7)
```

On public bits `(a,b)=(n_bit,M_bit)` and hidden start bits `(u,v)`, its total
transition is

```text
(S,d_i,d_j,z_i,z_j) |->
(D_(a,u,v)(S), High(d_i,u,b), High(d_j,v,b), z_i or u, z_j or v). (2.8)
```

The terminal weight is one exactly when `S` has no bad state,
`d_i,d_j<=0`, and both flags are set.  Hence it accepts exactly
`1<=i,j<=M` with no mismatch offset `k<n`.

For `a,b in {0,1}`, define the finite nonnegative integer matrix `A_ab` on `O`
by

```text
A_ab[q,r] = #{(u,v) in {0,1}^2 : delta_O(q;a,b,u,v)=r}.    (2.9)
```

Every row has total weight four.  Let `alpha` select the initial outer state
and `omega` be the terminal-weight column.  If `a_t,b_t` are synchronized
low-to-high binary digits of `n,M`, padded by high zeros, then

```text
C(n,M)=alpha A_(a_0 b_0) ... A_(a_(L-1) b_(L-1)) omega.   (2.10)
```

Equivalently,

```text
V(0,0)=omega,
V(2n+a,2M+b)=A_ab V(n,M),
C(n,M)=alpha V(n,M).                                      (2.11)
```

High-zero padding does not change the output: hidden high `1` bits violate
`i,j<=M`, while hidden zero bits preserve each admissible run.  This is an
exact finite-state recurrence; the enormous universal state set need not be
materialized as a dense matrix.

## 3. Decimation and the finite profile automaton

From (1.1), for `a>=1` and `r>=0`,

```text
p_(2a)=p_a,        p_(4r+1)=0,        p_(4r+3)=1.           (3.1)
```

Let `T(e,k)` be the alternating word of length `k` beginning with `e`.  Put
`h=ceil(n/2)` and `l=floor(n/2)`.  Separating even and odd absolute positions
gives

```text
B(2a,n)   = interleave(B(a,h),   T(a mod 2,l)),
B(2a+1,n) = interleave(T(a mod 2,h), B(a+1,l)).             (3.2)
```

The interleave always begins with its first argument.  Equations (3.2) expose
both endpoint shifts: even starts map to `a`, while odd starts map to `a+1` on
their second component.

Paperfolding also admits the following smaller, structure-specific alternating
profile automaton and scalar recurrence.  It is derived independently rather
than asserted to be a minimized quotient of (2.7).  Use five control states:

```text
E(s,t,n) : B(s,n)=B(t,n),
A_e(s,n) : B(s,n)=T(e,n),             e in {0,1},
K_e(s,n) : B(s,n)=e^n.                e in {0,1}.           (3.3)
```

Define the complete finite guards

```text
eta(c,d,k)   := (k=0) or (c=d),
gamma(c,d,k) := (k=0) or (k=1 and c=d).                    (3.4)
```

`eta` compares two alternating words.  `gamma` compares an alternating word
beginning with `c` with the constant word `d^k`.

### Complete E table

Every ordered start-parity pair occurs in exactly one row:

```text
E(2a,2b,n)     <=> E(a,b,h) and eta(a mod 2,b mod 2,l),
E(2a+1,2b+1,n) <=> eta(a mod 2,b mod 2,h) and E(a+1,b+1,l),
E(2a,2b+1,n)   <=> A_(b mod 2)(a,h) and A_(a mod 2)(b+1,l),
E(2a+1,2b,n)   <=> A_(a mod 2)(b,h) and A_(b mod 2)(a+1,l). (3.5)
```

### Complete A and K tables

For each `e in {0,1}`, both start parities occur:

```text
A_e(2a,n)   <=> K_e(a,h) and gamma(a mod 2,1-e,l),
A_e(2a+1,n) <=> gamma(a mod 2,e,h) and K_(1-e)(a+1,l),

K_e(2a,n)   <=> K_e(a,h) and gamma(a mod 2,e,l),
K_e(2a+1,n) <=> gamma(a mod 2,e,h) and K_e(a+1,l).          (3.6)
```

At `n=0`, every predicate in (3.3) is true.  There are four instantiated rows
in (3.5), four A rows, and four K rows: 12 total.  Hence every state, state
parameter `e`, and start-parity input has a transition.  `automaton_spec.json`
records these rows independently of this prose.

## 4. Exact collision recurrence

Write

```text
P_0(M)=floor(M/2),       P_1(M)=ceil(M/2),
R(M)=P_0(M)^2+P_1(M)^2.                                  (4.1)
```

These are respectively the counts of even starts, odd starts, and ordered
same-parity start pairs in `{1,...,M}`.

Let `z(M)=#{s<=M:p_s=1}`.  Splitting starts by parity in (3.1) gives

```text
z(0)=0,
z(M)=z(P_0(M))+floor(P_1(M)/2),
C(1,M)=z(M)^2+(M-z(M))^2.                                 (4.2)
```

For `r,e in {0,1}`, define the profile multiplicities

```text
AA_(r,e)(k,M)=#{s<=M:s mod 2=r and A_e(s,k)},
KK_(r,e)(k,M)=#{s<=M:s mod 2=r and K_e(s,k)}.              (4.3)
```

Their bases are

```text
AA_(r,e)(0,M)=KK_(r,e)(0,M)=P_r(M),
AA_(r,e)(n,0)=KK_(r,e)(n,0)=0.                            (4.4a)
```

The empty-bound row prevents a circular length-one call.  For `n>0,M>0`, the
complete count transitions induced by (3.6) are

```text
AA_(0,e)(n,M) = sum_[q=0,1] gamma(q,1-e,l) KK_(q,e)(h,P_0(M)),
AA_(1,e)(n,M) = sum_[q=0,1] gamma(q,e,h) KK_(1-q,1-e)(l,P_1(M)),

KK_(0,e)(n,M) = sum_[q=0,1] gamma(q,e,l) KK_(q,e)(h,P_0(M)),
KK_(1,e)(n,M) = sum_[q=0,1] gamma(q,e,h) KK_(1-q,e)(l,P_1(M)).       (4.4)
```

Let `S(n,M)` count the pairs in (1.3) whose starts have the same parity.  Then

```text
S(0,M)=R(M),
S(1,M)=C(1,P_0(M))+R(P_1(M)),
S(n,M)=S(h,P_0(M))+S(l,P_1(M))                 for n>=2.   (4.5)
```

The special `n=1` row is necessary: the length-zero half of (3.5) imposes no
parity guard.

Let `H(n,M)` count collisions oriented from an even start to an odd start.
Writing an odd start as `2b+1` and then putting `u=b+1` gives

```text
H(n,M) = sum_[r,q in {0,1}]
  AA_(r,1-q)(h,P_0(M)) * AA_(q,r)(l,P_1(M)).               (4.6)
```

The reverse orientation has the same count.  The exact full-prefix recurrence
is therefore

```text
C(n,M)=S(n,M)+2H(n,M).                                    (4.7)
```

Equations (4.1)--(4.7), with the finite states
`S,H,AA_(r,e),KK_(r,e),z`, are an exact recurrence for every `n,M`; no values
are fitted from a table.  They retain the literal occurrence multiplicities:
if `m_w=#{s<=M:B(s,n)=w}`, then (4.7) equals `sum_w m_w^2`.

There is a useful closed state elimination.  In (3.6), if `n>=4`, then either
`l>=2` in the even A row or `h>=2` in the odd A row, making its `gamma` guard
false.  Hence

```text
A_e(s,n) is false for every s,e when n>=4.                 (4.8)
```

Consequently `H(n,M)=0` for `n>=7`, and

```text
C(n,M)=S(n,M)
      =S(ceil(n/2),floor(M/2))+S(floor(n/2),ceil(M/2))      (4.9)
```

for every `n>=7`.  This does not mean that scalar `C` is closed under the same
formula at all lengths; Section 7 gives the smallest failure.

## 5. Induction proof of literal semantics

This section is the universal argument.  The replay ranges in Section 6 are
only transcription tests.

1. **Symbol induction.**  Before the least significant `1`, state `Z` is
   exact.  On that `1` the automaton enters `A`.  The next bit is exactly the
   low bit of `(oddpart(m)-1)/2`, so the transition enters `O0` or `O1` with
   output (1.1); later bits and the flush bits leave that state fixed.  Thus
   (2.1) computes every `p_m`.
2. **Decimation induction.**  Equation (3.1) follows by removing one factor of
   two from `2a`, while the odd part of `4r+1` or `4r+3` has `j` respectively
   even or odd.  Apply (3.1) pointwise to offsets `0,...,n-1`; even and odd
   offsets give (3.2), including lengths `h,l` and the `a+1` endpoint.
3. **Profile transition induction.**  Two interleavings are equal iff their
   corresponding components are equal.  Substitute (3.2).  Alternating versus
   alternating is exactly `eta`; alternating versus constant is exactly
   `gamma`.  This yields every iff in (3.5)--(3.6), not merely one direction.
   Since the tables exhaust all start parities, induction down the decimation
   tree decides the literal predicates (3.3).
4. **Multiplicity induction.**  Partition `{1,...,M}` into `2a` with
   `1<=a<=P_0(M)` and `2b+1` with `0<=b<P_1(M)`.  In the second class the map
   `u=b+1` is a bijection onto `{1,...,P_1(M)}` and reverses parity.  Counting
   the A/K iff rows over these two bijections gives (4.4).  Counting the four E
   rows gives (4.5)--(4.6).  Same-parity, even-to-odd, and odd-to-even pairs are
   a disjoint exhaustive partition, proving (4.7).
5. **Witness-automaton induction.**  After `t` low bits, a primitive state in
   `S` has `d=sign(k mod 2^t - n mod 2^t)`, carries obtained by dividing the
   processed sums `i+k,j+k` by `2^t`, and the two symbol states reached by the
   first `t` sum bits.  Moreover, `S` contains exactly the states produced by
   all `2^t` low-bit choices of `k`.  This is true initially, and
   (2.4)--(2.6) give the induction step.  In the outer weighted automaton,
   `d_i,d_j` compare processed residues with `M`, the flags record positivity,
   and path weight equals the number of processed `(i,j)` bit pairs reaching
   the state.  At a common full bit length, flushing and (2.5) make the terminal
   test exactly (1.3).  Expanding the four hidden bit pairs proves
   (2.9)--(2.11).
6. **Well-foundedness of the smaller recurrence.**  For `n>=2`, both child lengths are smaller.  At
   `n=1`, an even A/K child can retain length one but its bound changes from
   `M` to `floor(M/2)`.  Lexicographic induction on `(n,M)` therefore terminates
   at the explicit empty-bound base (4.4a), and proves that the recurrence
   returns exactly the literal ordered-pair count for every `n>=0,M>=0`.

This proves transition completeness and the claimed literal-pair invariant at
every recursive depth, conditional only on the explicitly defined
paperfolding model (1.1).

## 6. Self-contained replay

From a directory containing only the delivered files, run

```text
python3 verify_recurrence.py
sha256sum -c SHA256SUMS
```

The verifier checks:

- the canonical statement and primary-source hashes;
- all 8 symbol-DFAO and all 64 symbol tensor-square transitions;
- all `192*16=3072` primitive factor-pair transitions, row weight four, and
  automaton counts with two extra high-zero padding columns for every
  `0<=n<=12`, `0<=M<=32`;
- (3.1) through index 4096;
- 64,925 JSON-driven literal/profile transition instances, including start 1;
- 19,400 literal/profile multiplicity instances;
- (4.7) against direct `sum_w m_w^2` counts for every
  `0<=n<=24`, `0<=M<=96`;
- the vanishing gate (4.8) on lengths 4 through 64 at `M=512`;
- `C(7,48)=98`, the T91 regression target, and 28 distinct factors on the
  locally replayed recursive `P_7` transversal.

These finite checks are `experiment`; they test transcription and can falsify
the displayed recurrence, but the induction in Section 5 is the proof sketch.

## 7. Smallest closure falsifier

A tempting transfer drops the same-parity state `S` and auxiliary A/K states,
asserting the scalar recursion

```text
C(n,M) ?= C(ceil(n/2),floor(M/2))+C(floor(n/2),ceil(M/2)). (7.1)
```

The smallest failure with `n>=2`, ordered first by `n` and then `M`, is

```text
n=2, M=3:       C(2,3)=3,       right side of (7.1)=1+4=5. (7.2)
```

The verifier exhausts `M=0,1,2` first and checks equality there.  Thus (7.2)
is a cheap state-closure test: any proposed implementation that retains only a
scalar collision state is rejected before large computation.  A second,
multiplicity-specific gate is `C(7,48)=98`.  For self-contained replay define

```text
P_1={1,2,3,6},
P_(2k)=(2P_k-1) union (2P_k),
P_(2k+1)=(2P_k-1) union (2P_(k+1)).                        (7.3)
```

The verifier computes that `P_7` has 28 positions carrying 28 distinct
factors.  A representative-only synchronization therefore has weight 28 and
cannot count the 98 full-prefix pairs.  This is a finite `experiment`, not use
of the T91 sketch as a proved universal theorem.

## 8. Clause-by-clause comparison with T64

T64 below refers to the supplied machine-checked
`AggregateFejerCriterion.lean`, not the T91 sketch.

| T64 clause | T94 paperfolding statistic |
|---|---|
| Literal object: actual `piOrbit` and half-open base-10 parent/successor cylinders | Binary factors of the separately defined word (1.1); no circle orbit or cylinder identity |
| One row `1<=ell<m<=k` at the same cutoff `P=N(k)` | One factor length `n` and exactly `M` first starts; no triangular family or common pi prefix |
| Parent cutoff `40q^3`, successor cutoff `8000q^3`, two active-boundary terms in one weighted budget | Exact symbols have no half-open boundary term; none of these hypotheses is supplied |
| Collected circle-Fourier remainder at most `P^2/(10q)` | No Fourier coefficient occurs; tensor/profile transitions are combinatorial identities |
| Premises imply `QuantitativeSplittingLevel` and `rowThreshold` with constants `3281/7281`, `1/100` | T94 gives exact equality multiplicities only; it gives neither successor splitting nor those constants |

Therefore T94 is not an instance of T64 and supplies no fixed-pi Fourier
premise.

## 9. Clause-by-clause comparison with T83

T83 below refers to the supplied machine-checked
`T83LiteralStatisticAudit.lean`.

| T83 clause | T94 paperfolding statistic |
|---|---|
| `Q_pi` is ordered, diagonal-inclusive, strict circle near return | `C` is also ordered and diagonal-inclusive, but it is exact binary block equality, a strictly different predicate |
| Prescribed sample `L_n=10^(floor(n/2))` | `M` is an arbitrary declared number of starts; there is no claim at `L_n` for pi |
| Exact lag decomposition includes the diagonal and both orientations | (4.5)--(4.7) likewise retain the diagonal and both mixed orientations, but partition by parity rather than pi lag sectors |
| Unconditional residual short budget is `2L_n n` | T94 has exact finite mixed profiles and no metric short sector |
| Exact-long all-rates subexponential control conditionally implies the exact-collision entropy interface | T94 derives exact counts but no all-rates decay on the T83 scale and no statement about pi's decimal blocks |
| Near-return route additionally needs effective irrationality and residual-long all-rates control | T94 has neither premise and exact equality cannot replace strict near return |

Thus T94 does not claim T83's C7, exact-long premise, residual-long premise,
entropy conclusion, or any canonical statement for pi.

## 10. Pi-specific transfer hypothesis

**PF-to-T83 transfer hypothesis (conjecture, not asserted for pi).**  A return
to the named T83 frontier would require an exact pi-specific finite base-10
carry/recurrence system with all of the following properties:

1. states have literal semantics for equality of two decimal factors and for
   every boundary/carry profile created by decimating starts and lengths, just
   as `E,A_e,K_e` close (3.5)--(3.6);
2. every decimal input digit and every carry has a transition, with endpoints
   and full occurrence multiplicities preserved, not merely one canonical
   representative per factor;
3. the system either maps every strict T83 circle near return to an exact block
   equality plus one of finitely many proved metric-carry states, or remains
   explicitly on T83's exact-equality route;
4. its weighted recurrence proves the required all-rates residual-long or
   exact-long subexponential estimate at `M=L_n`, rather than only evaluating
   bounded prefixes.

The cheapest falsifier is state closure.  Instantiate every proposed state on
the two smallest nontrivial lengths and all one-digit start residues.  If two
instances assigned the same state have different successor profiles, or any
digit/carry transition leaves the proposed finite set, the transfer fails.
Even before a pi implementation exists, (7.2) shows that a scalar collision
state fails this test at `n=2,M=3`.  A survivor must at least retain the
same-parity and boundary-profile information represented by `S,A,K`; it must
then pass the full-multiplicity gate `C(7,48)=98` on the source model.

## 11. Conclusion

For regular paperfolding, the four-state symbol DFAO extends through the
192-state primitive tensor/carry layer and finite determinized outer universe
to the exact matrix recurrence (2.10)--(2.11).  The independent five-profile
decimation automaton yields the smaller exact collision recurrence
(4.1)--(4.7).  The inductions show that both constructions count literal
ordered pairs under the declared endpoint and overlap conventions.  This is a
low-description sibling mechanism only.  It supplies no evidence that pi has
a corresponding finite carry system and no conclusion about canonical C1, C2,
normality, decimal factor complexity, or digit occurrence for pi.
