# T38: Infinite continuation index of the balanced carry schedule

Status: `proof sketch`. The argument below is an exact prose argument, not a
Lean formalization. Its outcome supports C2 for the explicitly defined,
level-tagged balanced system.

## 1. Provenance, normalized target, and scope

- Canonical source: `knowledge/pi/statements/pi-digits.txt`.
- Canonical source SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
- Original external source URL: none. The canonical source is a human-authored
  local root recording Marcel's request of 2026-07-21.
- The canonical question V1 asks whether every finite decimal word, including
  words with leading zeroes, occurs contiguously in the decimal expansion of
  pi. T38 does not answer that question. It studies a structural sibling system
  derived from cross-base prefix compatibility.
- Machine-checked interface used below: T37,
  `TheoryLib.PiDigits.T37CrossBaseCarry`, staged as `CrossBaseCarry.lean`,
  SHA-256
  `be14ac145519d4a9e9f394365ef4852ad8196e37f3ddb7ee682b31b0dd0459a6`.

The agenda item is normalized as follows. At hexadecimal level `n`, the
decimal level is the unique integer `m_n` with

\[
             10^{m_n} \leq 16^n < 10^{m_n+1}.              \tag{1}
\]

A state records its level and both numeric prefixes. A transition appends one
hexadecimal digit and the one or two decimal digits required by (1). Schedule
legality, cylinder compatibility, and avoidance of the one-digit decimal word
`[2]` are all observable parts of a continuation. Myhill-Nerode equivalence
means equality of the resulting finite-continuation languages.

### Quantifiers and possible ambiguities

1. Levels range over all `n in N`, including the empty level `n=0`.
2. Although (1) says "integer", its solution is nonnegative, so `m_n` is used
   as a natural number in the T37 definitions.
3. Decimal prefixes and appended decimal blocks have fixed lengths. Leading
   zeroes are retained and are not erased by taking their numeric value.
4. All cylinders are T37's half-open cylinders. Compatibility means nonempty
   intersection, exactly as in T37.
5. Reachability starts at the empty state and uses only retained transitions.
6. The continuation alphabet is common to every level. A decimal block of
   length one and a decimal block of length two are different tagged symbols,
   even if both have numeric value zero.
7. The level tag and the balanced schedule are part of state behavior. A
   controller supplied with the future schedule by an external oracle is a
   different model and is not ruled out here.
8. No assertion concerns the branch selected by the hexadecimal or decimal
   digits of pi.

## 2. Exact interface with T37

For `b in {10,16}`, length `l in N`, and `0 <= P < b^l`, write

\[
 C_b(l,P)=\left[\frac{P}{b^l},\frac{P+1}{b^l}\right).
                                                               \tag{2}
\]

This is exactly `T37.prefixCylinder b l P`, and the bound on `P` is exactly
`T37.ValidPrefix b l P`. For hexadecimal length `n`, decimal length `m`, and
prefix values `A,D`, define

\[
 \kappa(n,m,A,D)=10^m A-16^nD.                               \tag{3}
\]

This is exactly `T37.carry n m A D`. The machine-checked theorem
`T37.cylinders_overlap_iff_carry_bounds` says

\[
 C_{16}(n,A)\cap C_{10}(m,D)\ne\varnothing
 \quad\Longleftrightarrow\quad
 -10^m<\kappa(n,m,A,D)<16^n.                                \tag{4}
\]

If an `r`-digit hexadecimal block of value `H` and an `s`-digit decimal block
of value `E` are appended, then

\[
 A'=16^rA+H,\qquad D'=10^sD+E,                              \tag{5}
\]

and `T37.carry_append` gives the exact identity

\[
 \kappa(n+r,m+s,A',D')
 =10^s16^r\kappa(n,m,A,D)+10^{m+s}H-16^{n+r}E.              \tag{6}
\]

No assertion from the unverified T36 note is used as a premise. Equations
(2)-(6) are definitions or machine-checked T37 results.

## 3. The balanced schedule

Let

\[
 \alpha=\log_{10}16,
 \qquad m_n=\lfloor n\alpha\rfloor.                         \tag{7}
\]

Here `10^alpha=16`, and real exponentiation by base 10 is strictly increasing.
Consequently

\[
 10^{m_n}\leq 10^{n\alpha}=16^n<10^{m_n+1},                \tag{8}
\]

so `m_n` satisfies (1). If an integer `m` also satisfies (1), strict
monotonicity gives `m <= n alpha < m+1`, hence
`m=floor(n alpha)=m_n`; this proves uniqueness. Since `16^n >= 1`, no negative
integer can satisfy the strict upper inequality in (1), so `m_n in N`.

Define the schedule increment

\[
                  \delta_n=m_{n+1}-m_n.                    \tag{9}
\]

Because `1<alpha<2`, adding `alpha` to a real number increases its floor by
either one or two. Thus

\[
                       \delta_n\in\{1,2\}.                 \tag{10}
\]

### Lemma 1: `alpha` is irrational

Suppose `alpha=p/q` with integers `p,q`, `q>0`, in lowest terms. Since
`alpha>0`, also `p>0`. Raising `10^alpha=16` to the `q`th power gives

\[
                         10^p=16^q.                         \tag{11}
\]

The left side has prime factorization `2^p 5^p`, while the right side is
`2^(4q)`. Uniqueness of prime factorization would force `p=0` from the exponent
of 5, contradicting `p>0`. Hence `alpha` is irrational.

### Lemma 2: no two increment tails are equal

For any distinct `n,k in N`, there is a `j in N` such that

\[
                    \delta_{n+j}\ne\delta_{k+j}.           \tag{12}
\]

It is enough to consider `n<k` and put `d=k-n>0`. If (12) failed for every
`j`, then

\[
                   \delta_{n+i}=\delta_{n+d+i}
                   \quad\hbox{for every }i\geq0.           \tag{13}
\]

Thus the increment sequence would be periodic with period `d` from level `n`
onward. Put

\[
 S=\sum_{i=0}^{d-1}\delta_{n+i}=m_{n+d}-m_n.                \tag{14}
\]

Telescoping (13), or induction on `r`, gives

\[
                       m_{n+rd}=m_n+rS                      \tag{15}
\]

for every `r in N`. On the other hand, (7) gives

\[
               0\leq (n+rd)\alpha-m_{n+rd}<1.              \tag{16}
\]

Divide (16) by `n+rd` and let `r` tend to infinity. Using (15), the left-hand
ratio tends both to `alpha` and to `S/d`. This makes `alpha=S/d` rational,
contradicting Lemma 1. The case `k<n` follows by exchanging `n` and `k`.

## 4. Reachable digit-2-avoiding states

For `s in {1,2}`, let `Dec_s` be the set of words of exactly `s` digits from
`{0,...,9}`. Let `Hex={0,...,15}`. The common transition alphabet is the
disjoint union

\[
             \Sigma=Hex\mathbin{\times}(Dec_1\mathbin{\sqcup}Dec_2). \tag{17}
\]

The disjoint union is important: it records block length independently of
numeric value. Write `[e]_10` for the fixed-length numeric value of a decimal
block `e`.

**Definition 1 (balanced state).** A level-`n` balanced state is a tuple

\[
                             q=(n,A,D)                       \tag{18}
\]

such that

\[
 0\leq A<16^n,\qquad 0\leq D<10^{m_n},                     \tag{19}
\]

the fixed-length `m_n`-digit representation of `D` contains no digit `2`, and

\[
 C_{16}(n,A)\cap C_{10}(m_n,D)\ne\varnothing.               \tag{20}
\]

By (4), condition (20) is equivalently the exact carry inequality

\[
             -10^{m_n}<\kappa(n,m_n,A,D)<16^n.              \tag{21}
\]

**Definition 2 (retained one-step transition).** Let `q=(n,A,D)` be a balanced
state and let `sigma=(h,e) in Sigma`. It is schedule-legal at `q` when
`|e|=delta_n`. For a schedule-legal symbol put

\[
 A'=16A+h,\qquad D'=10^{\delta_n}D+[e]_{10}.                \tag{22}
\]

There is a retained transition

\[
                   (n,A,D)\mathrel{\xrightarrow{\sigma}}
                   (n+1,A',D')                              \tag{23}
\]

exactly when the target satisfies Definition 1. Since
`m_{n+1}=m_n+delta_n`, (22) is T37's append operation with `r=1` and
`s=delta_n`; its new carry is therefore given exactly by (6). This definition
checks both full-prefix digit-2 avoidance and cylinder compatibility after the
append.

**Definition 3 (reachability).** The initial state is

\[
                            q_0=(0,0,0).                     \tag{24}
\]

A balanced state is reachable when a finite sequence of retained transitions
from `q_0` ends at that state.

**Definition 4 (continuation language).** For a reachable state `q`, a finite
word `w=sigma_0...sigma_{r-1} in Sigma*` is accepted from `q` when its symbols,
in order, define retained transitions at every intermediate state. The empty
word is accepted. Define

\[
                   L(q)=\{w\in\Sigma^*:w\hbox{ is accepted from }q\}. \tag{25}
\]

Thus membership in `L(q)` means precisely that every scheduled append remains
cylinder-compatible and digit-2-avoiding. A wrong decimal-block length is not
a scheduled append and is rejected.

**Definition 5 (Myhill-Nerode equivalence).** For any two reachable,
possibly different-level states, define

\[
                         q\equiv q'
                         \quad\Longleftrightarrow\quad
                         L(q)=L(q').                         \tag{26}
\]

This is an equivalence relation because equality of sets is an equivalence
relation. It is the right-language equivalence of this level-tagged transition
system.

## 5. An infinite pairwise distinguishable family

For every `n in N`, define

\[
                            z_n=(n,0,0),                     \tag{27}
\]

where `A=0` represents `n` hexadecimal zeroes and `D=0` represents `m_n`
decimal zeroes.

### Lemma 3: every `z_n` is a reachable balanced state

Both prefix bounds (19) hold. The decimal word consists only of zeroes, so it
avoids digit `2`. Its carry is

\[
                     \kappa(n,m_n,0,0)=0.                   \tag{28}
\]

Because `-10^(m_n)<0<16^n`, T37's criterion (4) proves compatibility.

For reachability, at each level `i` use the symbol

\[
                     a_i=(0,0^{\delta_i}),                  \tag{29}
\]

where the decimal component is the all-zero block of length `delta_i`.
Equation (10) puts `a_i` in the fixed alphabet `Sigma`, and it is
schedule-legal at level `i`. Equations (22) and (28) show that it takes `z_i`
to `z_(i+1)`, which is retained by the preceding compatibility and avoidance
check. Induction from `z_0=q_0` proves reachability of every `z_n`.

### Theorem 4: the states `z_n` are pairwise Myhill-Nerode inequivalent

Fix `n ne k`. By Lemma 2 the set

\[
       \{j\in\mathbb N:\delta_{n+j}\ne\delta_{k+j}\}       \tag{30}
\]

is nonempty. Let `j(n,k)` be its least member. The explicit distinguishing
continuation is

\[
 W_{n,k}=a_n a_{n+1}\cdots a_{n+j(n,k)},                    \tag{31}
\]

with the all-zero symbols `a_i` from (29).

Starting from `z_n`, every symbol in (31) has the required scheduled length
and takes one all-zero state to the next. Hence

\[
                             W_{n,k}\in L(z_n).              \tag{32}
\]

For every `i<j(n,k)`, minimality gives
`delta_(n+i)=delta_(k+i)`. Therefore the first `j(n,k)` symbols of the same
word (31) are schedule-legal from `z_k` and take it to `z_(k+j(n,k))`. The
last symbol has decimal length `delta_(n+j(n,k))`, while the schedule at that
state requires the different length `delta_(k+j(n,k))`. The last transition
is therefore not schedule-legal, so

\[
                             W_{n,k}\notin L(z_k).            \tag{33}
\]

Equations (32)-(33) give `L(z_n) ne L(z_k)`, hence `z_n` is not equivalent to
`z_k`. This works for every distinct pair, so (27) is an infinite family of
reachable, pairwise distinguishable states.

### Corollary 5: infinite index and finite-quotient obstruction

The equivalence (26) has infinitely many classes. In particular, no map from
all reachable states to a finite set can identify states only in a way that
preserves their complete continuation languages: by the pigeonhole principle
two members of the family (27) would receive the same quotient state, while
Theorem 4 supplies a continuation accepted from exactly one of them.

This is the infinite-family outcome requested by T38 and supports C2 for the
exact model of Definitions 1-5. It closes the arbitrary finite
language-preserving quotient gap for that model, rather than merely observing
that T37's exact reduced carry is unbounded.

## 6. What the result does and does not say

The separator (31) uses only exact all-zero prefixes and the arithmetic fact
that the balanced increment schedule has no repeated tails. It does not use a
bounded state table, digit search, minimization experiment, or finite sample.
There is no computational evidence in this note, and no bounded computation is
being labeled as evidence for a universal claim.

The infinite index includes schedule legality as observable behavior. If a
purported finite controller is additionally given the current level or the
entire future sequence `(delta_n)` by an external clock or oracle, then that
external object carries the infinitely many schedule tails. Such a controller
is not a finite quotient of the level-tagged continuation languages in (25).
Likewise, erasing decimal-block lengths or changing to an asynchronous symbol
encoding changes the language and poses a different question. This limitation
is explicit rather than hidden in the conclusion.

Most importantly, this structural sibling result proves nothing about pi,
`JMix(pi)`, canonical V1, or sibling V3. It neither proves that pi enters any
decimal cylinder nor uses any digit of pi. T37's conditional
`JMix_pi_implies_canonicalV1` theorem remains conditional, and no hypothesis
about `JMix(pi)` is supplied here.

## 7. Verification checklist and bounded reuse search

1. Check (2), (3), (4), and (6) against the named T37 declarations.
2. Check the unique schedule formula (7)-(10), including the irrationality
   proof in Lemma 1.
3. Check Lemma 2 by assuming equal tails, telescoping one period, and taking
   the elementary floor limit.
4. Check from (21) and (28) that every all-zero state is compatible and from
   (29) that it is reachable while avoiding digit `2`.
5. For each `n ne k`, check that (31) is accepted from `z_n` and rejected from
   `z_k` exactly at the first schedule-length mismatch.
6. Check that the conclusion is only infinite Myhill-Nerode index for
   Definitions 1-5, with the scope limitations of Section 6.

A bounded search of the supplied knowledge library on 2026-08-01 found the
unverified T36 note's explicit Myhill-Nerode gap and the machine-checked T37
carry interface. No claim of literature novelty is made for the standard
right-language definition or for this elementary balanced-schedule argument.
