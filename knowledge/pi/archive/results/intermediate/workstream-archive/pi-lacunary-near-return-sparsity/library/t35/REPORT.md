# T35: one-stream realization of moving-root windows

Status: `proof sketch`. The finite checks are an `experiment`. The cited T29
and T33 declarations are `machine-checked`; the new de Bruijn construction and
its asymptotic proof below are not claimed to be machine-checked.

## 1. Provenance, normalized statement, and scope

- Canonical statement: `canonical_statement.txt`, an artifact-local copy of
  `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. The package adds one
  terminal LF to the source's 4,026 bytes; the verifier removes exactly that
  transport byte and hashes the recovered source bytes.
- Original source URL: none. The canonical question was formulated locally by
  this program on 2026-07-22.
- SHA-256, rechecked by `verify_stream.py`:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Canonical A1 asks whether, for every integer `A >= 1`, every sufficiently
  large integer `n` admits an integer `N >= 1` such that
  `A*n*Q_pi(n,N) <= N^2`, with ordered pairs and the diagonal included.
- T35 is an artificial-stream A14 sibling. It makes no assertion about pi,
  C2, canonical A1, or decimal factor complexity of pi.

The question here is narrower. T33 machine-checks a moving-root/no-pullback
mechanism for abstract outgoing-conservative real count trees. We ask whether
the same mechanism can occur when every triangular row consists of overlapping
factor counts from prefixes of one infinite decimal stream. The answer below
is yes, although the literal nonstationary weights of T33 are not realizable.

The quantified target is:

1. one stream `x` is fixed before every row quantifier;
2. sampled-start checkpoints `N_q` and inspecting-prefix lengths `K_q` are
   strictly increasing;
3. row `q` contains exact counts at every length `0 <= n <= 2q`;
4. its moving window consists of the `q` consecutive edges
   `n=q,...,2q-1`;
5. cumulative T29 full selected-edge leakage divided by the collision energy
   at level `q` tends to zero;
6. the moving roots have absolute depth `q`, so they escape;
7. at the fixed threshold `1/2`, neither the fixed-coordinate limiting count
   tree nor the eventually stable original-coordinate predicate has a branch.

Ambiguities are resolved as follows. A path of length `q` has `q` edges and
`q+1` nodes. All extensions are right extensions. Counts use the first `N_q`
starting positions in the infinite stream, so right-extension conservation is
exact; `K_q` records how much finite prefix is sufficient to inspect the row.
Words and occurrences may overlap. A branch in recentered suffix coordinates
is not an original-coordinate branch. Positivity is required, and the
threshold `1/2` is fixed outside all branch quantifiers.

## 2. Exact stream-prefix counts and boundaries

Let `D={0,1,...,9}` and let `x=(x_j)_(j>=0)` be any stream in `D^N`. If
`w in D^n`, define the first-`N`-starts overlapping count

```text
C_N(w) = #{j : 0 <= j < N and x_j...x_(j+n-1)=w}.             (1)
```

The factor may use digits after position `N-1`; only its start is restricted.
A prefix of length at least `N+n-1` determines (1). This is exactly the
`blockCount` convention in the checked workspace code, rather than the
wholly-contained convention.

Write `I_j(w)` for the indicator that `w` starts at `j`. Direct partition of
the finite start set proves the following numbered identities for every
`N,n,w`:

```text
sum_(w in D^n) C_N(w) = N;                                      (2)

C_N(w) = sum_(d in D) C_N(wd);                                  (3)

sum_(d in D) C_N(dw) + I_0(w) = C_N(w) + I_N(w);                (4)

sum_d C_N(wd) - sum_d C_N(dw) = I_0(w)-I_N(w).                  (5)
```

Identity (3) has no boundary loss because the next digit exists in the
infinite stream. In (4), prepending shifts starts `0,...,N-1` to occurrences
of `w` at starts `1,...,N`. Thus (5) is the exact finite de Bruijn imbalance,
of absolute value at most one. They coincide with the workspace declarations
`sum_snoc_blockCount` and `sum_cons_blockCount_endpoint`, but T35 does not cite
their verification status or use them as premises: the argument here is the
displayed finite partition.

The compatibility between two checkpoints is equally exact. If `N' >= N`,
then

```text
C_(N')(w) = C_N(w) + sum_(j=N)^(N'-1) I_j(w).                   (6)
```

This monotone integer increment identity is absent from an arbitrary family
of conservative rows and is checked between all delivered finite stages.

For comparison, if `P=x_0...x_(K-1)` and only wholly-contained factors are
counted, put

```text
Chat_K(w) = #{j : 0 <= j <= K-n and P[j,j+n)=w}.                (7)
```

For `1 <= n < K`, exact right and left boundary bookkeeping gives

```text
sum_d Chat_K(wd) = Chat_K(w)-1_{w=suffix_n(P)};                 (8)

sum_d Chat_K(dw) = Chat_K(w)-1_{w=prefix_n(P)};                 (9)

sum_d Chat_K(wd)-sum_d Chat_K(dw)
  = 1_{w=prefix_n(P)}-1_{w=suffix_n(P)}.                       (10)
```

The verifier checks (8)-(10), but the construction uses (1), because only (1)
is literally a T29 natural count tree.

## 3. One explicit infinite stream and its checkpoints

For each integer `q>=1`, a cyclic decimal de Bruijn word of order `q` is a
cyclic word of length

```text
L_q = 10^q                                                     (11)
```

in which every `q`-digit word occurs at exactly one cyclic phase. Such a word
exists: take the directed graph with vertices `D^(q-1)` and one edge for each
`q`-word, directed from its length-`q-1` prefix to its length-`q-1` suffix.
Every vertex has indegree and outdegree ten, and the graph is strongly
connected because target digits can be appended successively. An Euler circuit
therefore reads a de Bruijn word. To remove choice, let `z_q` be the
lexicographically least linear representative, beginning with `q` zeros,
among the finitely many such cyclic words. The supplied verifier generates the
same canonical prefer-min representative by the FKM recursion and independently
checks the defining cyclic-factor property at each tested order.

Define integers recursively by

```text
A_1 = 0,
R_q = q^3(A_q+1),
A_(q+1) = A_q + (R_q+1)L_q.                                   (12)
```

Define the single infinite stream

```text
x = z_1^(R_1+1) z_2^(R_2+1) z_3^(R_3+1) ... .                 (13)
```

Thus `A_q` is the absolute start of stage `q`. The sampled-start checkpoint,
moving start, window length, and inspecting-prefix checkpoint are

```text
N_q = A_q + R_q L_q,
r_q = q,
h_q = q,
K_q = N_q + 2q.                                                (14)
```

The copy of `z_q` after the first `R_q` copies supplies all lookahead needed
for lengths at most `2q`. Since `2q<10^q=L_q`,

```text
N_q < K_q < A_(q+1) < N_(q+1) < K_(q+1).                     (15)
```

Hence `P_q=x[0,K_q)` is a strictly increasing sequence of actual finite
prefixes, and it determines every entry in the triangular row

```text
T_q = {C_(N_q)(w) : 0 <= |w| <= 2q}.                           (16)
```

All rows come from the same stream, and (6) relates every pair of rows.

## 4. Exact counts inside the de Bruijn core

For `q <= n <= 2q`, let `S_(q,n)` be the set of cyclic length-`n` factors of
`z_q`. The first `q` digits identify the phase, so

```text
|S_(q,n)| = L_q.                                                (17)
```

For every `q>=1`, `n>=0`, and word `w in D^n`, define the earlier-start error

```text
e_(q,n)(w) = #{j : 0 <= j < A_q and x[j,j+n)=w}.               (18)
```

Every `w in S_(q,n)` has a unique periodic successor digit
`delta_(q,n)(w)`. There is exactly one word at every earlier start, including
starts whose factor crosses a stage boundary, so

```text
sum_(w in D^n) e_(q,n)(w) = A_q.                               (19)
```

The starts `A_q,...,N_q-1` are exactly `R_q` complete cycles. Consequently,
for every `n` in the displayed range,

```text
C_(N_q)(w) = R_q+e_(q,n)(w),  if w in S_(q,n),
C_(N_q)(w) =     e_(q,n)(w),  otherwise;                       (20)

C_(N_q)(w delta_(q,n)(w)) >= R_q,
  w in S_(q,n), q <= n < 2q.                                   (21)
```

The child count in (21) is at most its parent count by (3). Equations
(17)-(21) account for every start and every stage-boundary overlap; there is
no assumption that an earlier factor stays within its earlier stage.

## 5. Dominance and full selected-edge leakage

For row `q` and level `q <= n < 2q`, declare exactly `S_(q,n)` dominant and
select `delta_(q,n)(w)`. Put

```text
alpha_q = R_q/(R_q+A_q).                                       (22)
```

By (19)-(21), a selected parent has count at most `R_q+A_q` and its child has
count at least `R_q`; hence every selected edge is positive and
`alpha_q`-dominant. Moreover

```text
A_q/R_q <= 1/q^3, so alpha_q -> 1.                             (23)
```

Define the ordered, diagonal-inclusive collision energy, retained selected
energy, and T29 full selected-edge leakage by

```text
E_q(n) = sum_(w in D^n) C_(N_q)(w)^2;                           (24)

Reta_q(n) = sum_(w in S_(q,n))
              C_(N_q)(w delta_(q,n)(w))^2;                     (25)

Leak_q(n) = E_q(n)-Reta_q(n).                                  (26)
```

This is full leakage: it includes all energy outside the selected parents and
all selected-parent energy not retained by the selected children. It is not
merely the mass of nondominant parents.

For a selected parent write its error as `e_w` and its selected child's error
as `f_w`. Exact right-extension gives `0<=f_w<=e_w`. Therefore

```text
0 <= Leak_q(n)
   <= sum_(w in S_(q,n)) (2R_q e_w+e_w^2)
      + sum_(w notin S_(q,n)) e_w^2
   <= 2R_q A_q+A_q^2.                                         (27)
```

The final inequality uses (19) and `sum_w e_w^2 <= (sum_w e_w)^2=A_q^2`.
Also, (17) and (20) give

```text
E_q(q) >= L_q R_q^2.                                           (28)
```

There are exactly `q` edge levels in the window. Combining (12), (27), and
(28) proves the explicit low-leakage estimate

```text
[sum_(n=q)^(2q-1) Leak_q(n)] / E_q(q)
 <= q(2R_q A_q+A_q^2)/(L_q R_q^2)
 <= 2/(q^2 L_q)+1/(q^5 L_q) -> 0.                             (29)
```

Thus the windows are arbitrarily long and their normalized full leakage tends
to zero. T29's machine-checked generic theorems apply at their stated scope
because (2)-(3) make each encoded row a natural base-10 count tree. No T29
theorem is used to assert compatibility between rows; that is supplied by the
single stream and identity (6).

## 6. Moving roots and the tangent branch

Let `u_q` be the cyclic length-`q` factor of `z_q` at phase zero. Continue it
with periodic digits `a_(q,0),...,a_(q,q-1)` from `z_q`, and put
`v_(q,i)=a_(q,0)...a_(q,i-1)`, with `v_(q,0)` empty. At each absolute factor
depth `q+i`, equation (21) and the parent bound prove

```text
C_(N_q)(u_q v_(q,i+1))
 >= alpha_q C_(N_q)(u_q v_(q,i)) > 0                           (30)
```

for every `0<=i<q`. Define the normalized recentered profile for `|v|<=q` by

```text
p_q(v) = C_(N_q)(u_q v)/C_(N_q)(u_q).                         (31)
```

It satisfies `p_q(empty)=1`, `0<=p_q(v)<=1`, and exact outgoing conservation
inside the window by (3). The upper bound follows because occurrence of a
descendant implies occurrence of its prefix at the same sampled start.
Equation (30) is the required normalized dominance inequality. Hence these
actual stream rows satisfy every field of T33's `MovingRootRow`, after
reindexing `q=1,2,...` by natural numbers. We have

```text
h_q=q -> infinity, r_q=q -> infinity, alpha_q -> 1.            (32)
```

T33's machine-checked `exists_movingRoot_tangent_branch` therefore supplies,
after one subsequence, a conservative suffix-coordinate tangent profile and
an infinite threshold-one dominant branch in that tangent. This invocation is
only at T33's checked compactness scope. It does not identify suffix words
with fixed absolute words of `x`.

## 7. Exact original-branch quantifier and its failure

The phrase "original branch" needs care for a triangular family. A claim that
each fixed finite-`N` count tree has no branch would be false: among finitely
many sampled infinite suffixes, one can follow an eventual equivalence class
whose selected child retains all its count. The relevant pullback question is
whether one fixed absolute word and one fixed continuation work stably as the
checkpoints increase.

For fixed `beta>0` and a continuation `a:N->D`, write
`v_i=a_0...a_(i-1)`, with `v_0` empty. Define

```text
StableOriginalBranch(beta) :<=>
  there exist r>=0, u in D^r, and a:N->D such that
  for every i>=0 there exists Q_i such that for every q>=Q_i,
    C_(N_q)(u v_(i+1)) >= beta C_(N_q)(u v_i) > 0.             (33)
```

The root, continuation, and threshold are outside every row quantifier.
Allowing `Q_i` to depend on `i` makes (33) weaker than demanding one common
row cutoff, so disproving (33) also disproves that stronger reading.

Fix a word `w` of length `n`. For every `q>=n`, each `n`-word occurs exactly
`L_q/10^n` times in one de Bruijn cycle. If `B_q=R_qL_q`, then

```text
C_(N_q)(w) = B_q/10^n+e_(q,n)(w),  0<=e_(q,n)(w)<=A_q;         (34)

|C_(N_q)(w)/N_q-10^(-n)| <= A_q/N_q
 <= A_q/(R_qL_q) <= 1/(q^3L_q) -> 0.                          (35)
```

Thus the fixed-coordinate empirical tree exists and is

```text
p_*(w)=10^(-|w|).                                               (36)
```

It obeys both incoming and outgoing de Bruijn balance, and every child ratio
is exactly `1/10`. For any fixed `u,d`, (35) also makes
`C_(N_q)(ud)/C_(N_q)(u) -> 1/10`. Therefore the first edge in (33) eventually
fails whenever `beta>1/10`. In particular,

```text
not StableOriginalBranch(1/2),                                 (37)
```

and the actual limiting tree (36) has no `1/2`-dominant edge, hence no such
branch from any fixed root. This is the required absence of an original
fixed-threshold branch. It is compatible with the threshold-one tangent
branch because the tangent roots move to depths `q->infinity` before limits
are taken.

## 8. What de Bruijn balance does obstruct

Equation (5), divided by `N_q`, shows that every fixed-coordinate empirical
limit along checkpoints tending to infinity is stationary: incoming and
outgoing marginals agree. The literal T33 `separatorCount` is not stationary.
Its level-zero edge sends all mass to digit zero, so
`separatorCount([0])=1`; level one is a separator, so

```text
sum_(d in D) separatorCount([d,0])=separatorCount([0,0])=1/10. (38)
```

Thus the exact T33 weights cannot be the fixed-coordinate empirical limit of
one stream. This is not an obstruction to the mechanism tested by T35:
(29)-(32) realize arbitrarily long escaping moving windows, while (35)-(37)
forbid original pullback. The construction replaces T33's nonstationary
shallow tree by the stationary uniform tree forced by genuine overlaps.

## 9. Reproduction and finite model

The bundle includes the canonical statement as `canonical_statement.txt` with
the one transport LF documented in Section 1. The verifier reads only this
artifact-local file, removes exactly that byte, and rejects the recovered source
unless its hash is the value recorded in Section 1. No workspace parent or
external file is needed. From this artifact directory, run `sh reproduce.sh`.
Equivalently, run
`python3 -B verify_stream.py --max-order 2` there. The script uses only integer
arithmetic and `fractions.Fraction`. It deterministically generates the first
two stages, enumerates overlapping factors directly, and checks:

1. the bundled canonical statement hash and each cyclic de Bruijn property;
2. strict checkpoint nesting and sufficient finite-prefix lookahead;
3. identities (2)-(6) for every represented word;
4. wholly-contained boundary identities (8)-(10);
5. formulas (17)-(21), including all earlier and crossing starts;
6. every selected dominance inequality, energy, retained energy, and leakage;
7. the exact bound (29) by integer cross multiplication;
8. the displayed moving path and every shallow finite `1/2`-edge test.

For `q=2` it obtains

```text
A_2=20, R_2=168, L_2=100, N_2=16820, K_2=16824,
alpha_2 >= 168/188,
(E_2(2),E_2(3),E_2(4))=(2829160,2822774,2822772),
(Leak_2(2),Leak_2(3))=(6423,37),
sum Leak/E_2(2)=6460/2829160.
```

`raw_output.json` records the complete replay. These bounded checks are an
`experiment`; the universal quantifiers are discharged by (11)-(37), not by
finite enumeration.

## 10. Conclusion

The single explicitly specified stream (13), its nested finite prefixes
`P_q`, and its start checkpoints `N_q` produce genuine integer overlapping
factor-count triangles. Their escaping length-`q` windows have normalized full
leakage tending to zero and satisfy T33's checked moving-root hypotheses, yet
their stationary fixed-coordinate limit has child ratio `1/10` everywhere
and admits no fixed-threshold `1/2` branch. Conservation and de Bruijn balance
forbid the literal T33 separator weights but do not force pullback once roots
escape.

REALIZABLE
