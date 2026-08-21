# T15: Decimal words forced by the boundary branch

Status: `proof sketch` (a self-contained paper proof importing the
machine-checked T14 theorem; this note is not itself a Lean formalization).

## 1. Provenance, imported result, and scope

- Agenda item: T15, serving G10.
- Canonical source: `knowledge/pi/statements/pi-quantitative-block-hitting.txt`.
- Canonical source URL: none; this is a local problem formulation whose source
  file records its provenance.
- Canonical source SHA-256:
  `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`.
- Imported accepted artifact:
  `knowledge_library/t14/T14BoundaryRobustFejerDichotomy.lean`, SHA-256
  `da5f190dd776ebb211ada5960c17e0e0580adce5d9c2e0d9b670b16245b31c33`.
- Reused exact C1 definitions:
  `knowledge_library/t1/PiQuantitativeBlockHitting.lean`, SHA-256
  `e8c6034d7985ce986ba7f7af3905570ccfc18a348c925437f6ca40efb2505e90`.
- Reused decimal-cylinder API:
  `TheoryLib/PiDigits/T20BaseTenOrbitDensity.lean`, SHA-256
  `202d6db7dfc2f19db81c3cb96b856d36969652e54099c43e0d51b6ab62913126`.
- The exact imported theorem is
  `Theory.PiDigits.BoundaryRobustFejerDichotomy.not_C1_implies_unbounded_boundary_or_aggregated_resonance`.
  Its exact-deadline contrapositive companion is
  `pi_fullContainment_at_exact_deadline_of_smallness`.

This note translates only T14's boundary alternative into decimal-word
counts. It neither reproves T14's Fourier analysis nor asserts canonical C1.

## 2. Normalized statement and conventions

Fix positive natural numbers

```text
C >= 1,  K >= 1,  r >= 1.
```

Assume `not C1`. Then there are an integer `k >= K`, a length-`k` word `w`,
and its numerical value `a` (leading zeroes retained by padding to exactly
`k` digits) such that, on writing

```text
q = 10^k,       s = 10^r,       Q = qs = 10^(k+r),
D = Ckq,        N = D-k+1,
```

the word `w` has no occurrence at a start `0 <= n < N`. Equivalently, the
half-open cylinder

```text
I_a = [a/q,(a+1)/q) subset [0,1)
```

contains none of the canonical representatives

```text
x_n = fract(10^n pi),       0 <= n < N.
```

For every integer cutoff `M >= 0` satisfying

```text
M+1 >= 2*10^(2k+r),                                      (2.1)
```

one of the following holds:

1. T14's aggregated signed-frequency sum satisfies

```text
sum_(0<|h|<=M)
  (1-|h|/(M+1)) |sin(pi h/q)|/(pi |h|)
  * |sum_(n=0)^(N-1) exp(2 pi i h x_n)|
    >= N/(2q);                                            (2.2)
```

2. one of the two exterior length-`k+r` words immediately adjacent to
   `I_a` occurs at at least `N/(8q)` of the same starts `0 <= n < N`.
   Equivalently, its integer count is at least

```text
ceil(N/(8q)) = (N+8q-1) div (8q).                         (2.3)
```

Here and below inequalities involving counts and the fractions in (2.2)-(2.3)
are inequalities in the reals after casting the counts. The starts are exactly
the starts admissible for full containment of a length-`k` word by deadline
`D`. A counted length-`k+r` word can use the next `r` digits after `D`; thus
the statement does **not** claim that those longer words are fully contained
by `D`. They are fully contained by `D+r`.

### Quantifier and endpoint audit

- `C` and `K` are arbitrary positive integers; therefore the bad `k` are
  unbounded.
- `r` is any positive integer. It is fixed before T14 is specialized, but the
  resulting bad `k,w` supplied by T14 do not depend on `r`.
- For the resulting `k,w`, conclusion (2.2) or (2.3) holds for every `M`
  satisfying (2.1).
- Cylinders use canonical representatives in `[0,1)` and are half-open.
- Boundary distance is circular and strict: distance `< 1/Q`.
- Every relevant exact endpoint is excluded for the pi orbit in Section 5.
- Leading-zero words and the all-zero/all-nine wraparound words are included.

## 3. The four fine cylinders around the two boundaries

For `0 <= b < Q`, put

```text
J_b = [b/Q,(b+1)/Q).
```

Arithmetic on a fine-cylinder label in this section is modulo `Q`, always
returned as its canonical representative in `{0,...,Q-1}`. Define

```text
P = (as-1) mod Q,                 L = as,
R = (a+1)s-1,                    S = (a+1)s mod Q.           (3.1)
```

The letters stand for predecessor, left interior, right interior, and
successor. Since `0 <= a < q`, the unreduced labels `L` and `R` already lie in
`{0,...,Q-1}`. Only `P` can wrap when `a=0`, and only `S` can wrap when
`a=q-1`.

Let `digits_k(t)` denote the base-ten expansion of `0 <= t < 10^k`, padded on
the left to exactly `k` digits, and let `0^r` and `9^r` denote strings of `r`
zeroes and nines. The four labels in (3.1) encode exactly these words:

| label | ordinary case | wraparound case |
|---|---|---|
| `P` | if `a>0`, `digits_k(a-1) 9^r` | if `a=0`, `9^(k+r)` |
| `L` | `digits_k(a) 0^r` | no special case |
| `R` | `digits_k(a) 9^r` | no special case |
| `S` | if `a<q-1`, `digits_k(a+1) 0^r` | if `a=q-1`, `0^(k+r)` |

This table includes every carry case. Indeed, for `a>0`,

```text
as-1 = (a-1)s+(s-1),
```

and `s-1` is exactly `r` nines. Thus any borrow through trailing zeroes of the
`k`-digit representation of `a` is already the ordinary base-ten subtraction
`a-1`; for example `1200...0` becomes `1199...9` before the final `r` nines
are appended. Similarly,

```text
(a+1)s-1 = as+(s-1),
```

so `R` is `w` followed by `r` nines without carrying into `w`. For `S`, all
carries inside `a+1` are included before appending the zeroes. The terminal
carry `a=q-1 -> a+1=q` is precisely the circular reduction `Q mod Q=0`.
The terminal borrow `a=0 -> as-1=-1` is precisely `-1 mod Q=Q-1`.

Because `q,s >= 10`, the four canonical labels are pairwise distinct. At the
left boundary `a/q=as/Q`, the two adjacent fine cylinders are `J_P,J_L`; at
the right boundary `(a+1)/q=(a+1)s/Q mod 1`, they are `J_R,J_S`. This remains
literal when a boundary is `0 mod 1`: `J_(Q-1)` lies immediately to its left
on the circle and `J_0` immediately to its right.

## 4. Exact circular boundary-to-cylinder lemma

Let

```text
E_Q = {j/Q : 0 <= j < Q}
```

in canonical representatives. The omitted real endpoint `1` represents the
same circle point as the included endpoint `0`. If `x in [0,1) \ E_Q`, then

```text
min(d_T(x,a/q), d_T(x,(a+1)/q)) < 1/Q
  iff x in J_P union J_L union J_R union J_S.                (4.1)
```

**Proof.** We first prove the one-boundary assertion. Write a boundary as
`m/Q mod 1`, and let `c=floor(Qx)`. Since `x` is not a `Q`-adic endpoint,

```text
c/Q < x < (c+1)/Q.                                          (4.2)
```

Choose the integer lift of `m/Q` nearest along the circular arc witnessing
distance `<1/Q`. Multiplication by `Q` shows

```text
|Qx-m-zQ| < 1
```

for some integer `z`. By (4.2), the only possible canonical cell labels are
`m-1` and `m` modulo `Q`. Conversely, every nonendpoint point in either of
those two cells has circular distance strictly less than `1/Q` from the common
boundary. Hence

```text
d_T(x,m/Q)<1/Q
  iff x belongs to J_((m-1) mod Q) or J_(m mod Q).           (4.3)
```

Apply (4.3) first with `m=as`, obtaining `J_P union J_L`, and then with
`m=(a+1)s`, obtaining `J_R union J_S`. Their union is disjoint because the
four labels are distinct. This proves (4.1), including `m=0` and `m=Q`, since
all labels and distances in (4.3) are circular. QED

The deletion of `E_Q` is essential for this exact half-open formulation. At an
outer endpoint exactly `1/Q` from a coarse boundary, T14's strict neighborhood
excludes the point while one adjacent half-open `J_b` includes it. Section 5
proves that this issue never occurs for the pi orbit rather than changing
T14's endpoint convention.

## 5. Pi has no exact boundary hits

For every `n >= 0` and every integer `j` with `0 <= j < Q`, one has

```text
x_n != j/Q.                                                  (5.1)
```

These are all `Q`-adic circle endpoints in canonical representatives. If
equality held, the definition of fractional part would give an integer `z`
with

```text
10^n pi = z+j/Q,
```

and hence

```text
pi = (Qz+j)/(Q*10^n),
```

a rational number. This contradicts the standard theorem `irrational_pi`
(already used in `TheoryLib/PiDigits/T11PiDigitFactorComplexity.lean`). Thus
every `x_n` satisfies the nonendpoint hypothesis of (4.1). In particular, the
coarse endpoints, the two outer endpoints of the boundary neighborhoods, and
all possible wraparound representatives are excluded at once.

## 6. Fine cylinders are exactly long decimal words

For a length-`ell` decimal word `v`, let `[v]` be its numerical value, including
leading zeroes, and put `Q_ell=10^ell`. For `x in [0,1)`, the first `ell`
floor-based decimal digits of `x` equal `v` if and only if

```text
x in [[v]/Q_ell,([v]+1)/Q_ell).                              (6.1)
```

The forward implication is the only direction not named separately in the
accepted T14 API, so here is a direct proof. Put

```text
F_j = floor(10^j x),       0 <= j <= ell.
```

Since `0 <= x < 1`, `F_0=0`. The floor-based digit definition and Euclidean
division give

```text
F_(j+1) = 10 F_j + digit_j(x).                               (6.2)
```

Induction in (6.2) says that `F_ell` is exactly the numerical value of the
first `ell` digits. Those digits equal `v` precisely when `F_ell=[v]`.
Finally, the defining property of the floor gives

```text
F_ell <= 10^ell x < F_ell+1,
```

which is equivalent to (6.1). The reverse implication also follows directly,
and is machine-checked as the imported T20 lemma
`decimalDigit_eq_of_mem_wordCylinder`, used by T14's
`pi_digits_of_mem_wordCylinder`. This proves the claimed equivalence without
choosing between dual decimal expansions at rational endpoints; the
floor-based half-open convention chooses the terminating representative.

Applying (6.1) to `x_n=fract(10^n pi)` and using T20's shift theorem
`decimalDigit_baseTenOrbit` identifies membership in `J_b` with occurrence,
at start `n`, of the unique length-`k+r` word with value `b`. Define

```text
Occ_N(v) = #{0 <= n < N : the digits at n,...,n+k+r-1 equal v}.
```

Write T14's boundary count at this width as

```text
B_a(1/Q)
  = #{0 <= n < N :
      d_T(x_n,a/q)<1/Q or d_T(x_n,(a+1)/q)<1/Q}.
```

By Sections 4-5, it is exactly

```text
B_a(1/Q)
  = Occ_N(P)+Occ_N(L)+Occ_N(R)+Occ_N(S).                     (6.3)
```

This is equality of index counts, so repeated orbit values would retain their
multiplicity.

## 7. Removing exactly the two cylinder-interior words

The fine cylinders `J_L` and `J_R` are both contained in `I_a`. Algebraically,

```text
J_L = [a/q, a/q+1/Q),
J_R = [(a+1)/q-1/Q, (a+1)/q),                               (7.1)
```

and `1/Q < 1/q` because `r>=1`. Digitally, `L=w0^r` and `R=w9^r`, so either
long word has `w` as its first `k` digits. Since `w` is missing at every start
`n<N`, both counts vanish:

```text
Occ_N(L)=Occ_N(R)=0.                                         (7.2)
```

No exterior word is removed: `J_P` lies outside `I_a` immediately before its
left endpoint and `J_S` lies outside immediately after its right endpoint,
with the same statement on the circle for `a=0` and `a=q-1`. Combining
(6.3)-(7.2) gives the exact identity

```text
B_a(1/Q)=Occ_N(P)+Occ_N(S).                                  (7.3)
```

Therefore T14's boundary alternative

```text
B_a(1/Q) >= N/(4q)                                          (7.4)
```

implies

```text
max(Occ_N(P),Occ_N(S)) >= N/(8q).                            (7.5)
```

Indeed the maximum of two nonnegative numbers is at least half their sum.
Because the two counts are integers, (7.5) is equivalent to the explicit
integer bound (2.3). This is the requested count constant; no asymptotic or
hidden constant is present.

## 8. Specializing T14 at exact full-containment deadlines

T14 proves that `not C1` implies the following for every `C,K>=1`: there are
`k>=K`, a word `w`, and its label `a` for which

```text
D=Ck10^k,       N=D-k+1,                                    (8.1)
```

`w` is absent at every start satisfying `n+k<=D`, and the corresponding
cylinder is empty among `x_0,...,x_(N-1)`. Since `k<=D`, elementary natural
number arithmetic gives the exact equivalence

```text
n<N  iff  n+k<=D.                                            (8.2)
```

Thus there are exactly `N`, not `D` or `D-k`, admissible starts.

Now choose

```text
delta = 1/10^(k+r) = 1/Q.                                   (8.3)
```

T14 requires

```text
0<delta,
delta <= 1/(2q),
2q <= (M+1)delta.                                            (8.4)
```

The first condition is immediate. Since `r>=1`, `s=10^r>=10>=2`, and hence

```text
1/(qs) <= 1/(2q).
```

For the cutoff, substitution of `delta=1/(qs)` gives the exact equivalences

```text
2q <= (M+1)/(qs)
  iff 2q^2 s <= M+1
  iff 2*10^(2k+r) <= M+1,                                   (8.5)
```

which is hypothesis (2.1).

Apply T14's
`not_C1_implies_unbounded_boundary_or_aggregated_resonance` with (8.3)-(8.5).
Its Fourier alternative is exactly (2.2). In its boundary alternative, apply
the exact count identity (7.3) and the pigeonhole estimate (7.5), obtaining
(2.3) for either the predecessor word `P` ending in `r` nines or the successor
word `S` ending in `r` zeroes. This proves the normalized statement in
Section 2. QED

For comparison, the imported theorem
`pi_fullContainment_at_exact_deadline_of_smallness` is the strict
contrapositive at the same deadline: if every boundary count is `<N/(4q)` and
the aggregated sum is `<N/(2q)`, every length-`k` word occurs with
`n+k<=D`. Our argument uses the logically equivalent necessary direction at
the missing word and does not reverse either obstruction branch.

## 9. Complete carry and wraparound audit

The four possible positions of `a` are summarized explicitly:

| case | predecessor `P` | interior `L` | interior `R` | successor `S` |
|---|---|---|---|---|
| `a=0` | `9^(k+r)` | `0^k 0^r` | `0^k 9^r` | `digits_k(1) 0^r` |
| `0<a<q-1` | `digits_k(a-1) 9^r` | `w0^r` | `w9^r` | `digits_k(a+1) 0^r` |
| `a=q-1` | `digits_k(q-2) 9^r` | `9^k 0^r` | `9^(k+r)` | `0^(k+r)` |

The middle row includes all internal borrow/carry chains in `a-1` and `a+1`.
In the first row the left endpoint is `0`; in the last row the right endpoint
is `1=0 mod 1`. Notice that `9^(k+r)` can be an exterior word in the first row
and an interior word in the last row. These concern different missing
cylinders and create no overlap within one four-cylinder decomposition.

## 10. Exact limitations

- This is a necessary-only consequence of `not C1` through T14.
- There is no converse: frequent occurrence of one adjacent suffix word, or a
  large aggregated Fourier sum, does not imply that the central word is
  missing and does not imply `not C1`.
- The proof supplies no upper bound for either adjacent-word count in the pi
  digit stream and no independent estimate for T14's aggregated sum.
- The long-word count is taken over the exact base-word start range `n<N`; it
  is not a cover-time statement for length `k+r`.
- No finite computation about pi is used as proof.
- Consequently this note neither proves nor refutes C1 and leaves C1 `open`.

## Imported references

- [T14] `knowledge_library/t14/T14BoundaryRobustFejerDichotomy.lean`, in
  particular `twoBoundaryCount`, `aggregatedFourierSum`,
  `not_C1_implies_unbounded_boundary_or_aggregated_resonance`, and
  `pi_fullContainment_at_exact_deadline_of_smallness`.
- [T20] `TheoryLib/PiDigits/T20BaseTenOrbitDensity.lean`, in particular
  `decimalDigit_baseTenOrbit`, `decimalDigit_eq_of_mem_wordCylinder`, and
  `wordValue`.
- [T1] `knowledge_library/t1/PiQuantitativeBlockHitting.lean`, for the exact
  definition of C1 and its zero-based full-containment convention.
