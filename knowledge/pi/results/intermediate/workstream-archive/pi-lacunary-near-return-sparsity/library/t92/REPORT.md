# T92: constant-run Review-B discriminator

Claim label: **machine-checked** for the declarations in Section 8. The
universal Review-B inequality remains a **conjecture**. This note makes no
fixed-pi, C1, or C2 claim.

## 1. Immutable canonical scope

The vendored `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

and is byte-identical to
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. For integers `n,N>=1`,
the canonical count is

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.       \tag{1.1}
\]

Pairs are ordered, all `N` diagonal pairs are included, and the cutoff is
strict. The open canonical statement is exactly

\[
 \forall A\in\mathbb N_{\ge1}\ \exists n_0\ge1\ \forall n\ge n_0\
 \exists N\ge1:\quad AnQ_\pi(n,N)\le N^2.                 \tag{1.2}
\]

Thus `N` may depend on `A,n`. T92 concerns an exact-word sibling only and does
not assert (1.2).

## 2. Exact program-qualified T56/C7 quotation

The relevant T56 is

```text
TheoryLib/PiPositiveDecimalFactorEntropy/T56T56LagSectorAudit.lean
namespace DecimalFactorComplexity.T56LagSectorAudit
```

not the T56 note in the present pi-lacunary program. Its C7 comes from
`PiPositiveDecimalFactorEntropy/T26T26SparseLongBandFejer.lean`, with the
near-return equivalence in T27. T83's promoted Lean module imports these exact
declarations.

With natural-number division, set

\[
 L_n=10^{\lfloor n/2\rfloor},\qquad H_n=\lfloor10^n/2\rfloor. \tag{2.1}
\]

For `n>=1`, `2H_n=10^n`. The complete triangular Fejer energy is

\[
 \mathcal F_\pi(L,H)=
 \sum_{\substack{h\in\mathbb Z\\|h|<H}}
 \left(1-\frac{|h|}{H}\right)
 \left|\sum_{j=0}^{L-1}e^{2\pi i h\{10^j\pi\}}\right|^2.  \tag{2.2}
\]

The frequency range is strict, signed, and includes `h=0`. The literal C7
quantifiers and normalization are

\[
 \boxed{\exists C\in\mathbb R\ (C>0)\ \exists N\in\mathbb N\ (N\ge1)\
 \ \forall n\in\mathbb N\ (n\ge N):
 \mathcal F_\pi(L_n,H_n)\le C H_nL_n.}                    \tag{2.3}
\]

T83's `literal_C7_iff_quantifiers` checks (2.3). Its
`literal_C7_iff_nearReturn_linear` checks the exact equivalent finite
statistic

\[
 \boxed{\mathrm{C7}\iff
 \exists A\in\mathbb R\ (A>0)\ \exists N\in\mathbb N\ (N\ge1)\
 \ \forall n\in\mathbb N\ (n\ge N):
 Q_\pi(n,L_n)\le A L_n.}                                  \tag{2.4}
\]

Here `Q_pi` still means ordered, diagonal-inclusive, strict circular near
returns. It is not exact block equality.

For `n>=1`, T56's exact lag decomposition is

\[
 Q_\pi(n,L_n)=L_n+2\sum_{r=1}^{L_n-1}
 \#\{0\le j<L_n-r:
 \|10^j(10^r-1)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.     \tag{2.5}
\]

The factor two gives both orientations and `L_n` is exactly the diagonal.
For parameters `mu,c,Q0`, T56 partitions this as

\[
 Q_\pi(n,L_n)=L_n+X_n+S_n^{\rm res}+T_n^{\rm res}.         \tag{2.6}
\]

The residual short range is exactly

\[
 0<r<n,\qquad r<L_n,\qquad 0\le j<L_n-r,                  \tag{2.7}
\]

and the residual long range is exactly

\[
 0<r,\qquad n\le r<L_n,\qquad 0\le j<L_n-r.              \tag{2.8}
\]

Residual starts satisfy the strict near-return in (2.5) and fail T56's
explicit `ArithmeticExcluded` predicate. Under the still-unproved premise
`EffectiveIrrationality Real.pi mu c Q0`, T56 checks `X_n=0`. Unconditionally,

\[
 S_n^{\rm res}\le 2L_nn.                                  \tag{2.9}
\]

This is an `O(nL_n)` bound, not the uniform `O(L_n)` bound in (2.4).

## 3. Review B's separate exact-word sibling

The Review-B claim does not use the carry-thickened relation above. Its
T87-normalized exact reading is as follows. For every integer `b>=2`, there
should exist `C_b>=0` such that, for every integer `n>=1`, with

\[
 L=b^{\lfloor n/2\rfloor},                                \tag{3.1}
\]

and every word `x` of length at least `L+n-1`, define

\[
 S_x^=(n,L)=\#\{(i,j):0\le i,j<L,\ 0<|i-j|<n,
 x[i,i+n)=x[j,j+n)\},                                     \tag{3.2}
\]

\[
 R_x^=(n,L)=\#\{(i,j):0\le i,j<L,\ |i-j|\ge n,
 x[i,i+n)=x[j,j+n)\}.                                     \tag{3.3}
\]

Both counts are ordered and off-diagonal. The short cutoff is strict; the
long cutoff includes lag `n`; there are exactly `L` starts, so the required
word length is `L+n-1`. The universal claim is

\[
 \boxed{\forall b\ge2\ \exists C_b\ge0\ \forall n\ge1\ \forall x:
 S_x^=(n,L)\le C_bL+\frac32R_x^=(n,L).}                   \tag{RB}
\]

The constant may depend only on `b`, not on `n` or `x`. T83 correctly left
this as a conjecture. T92 tests one infinite binary family; it does not prove
or refute `(RB)` universally.

## 4. The one legal infinite family

Fix `b=2` and use one stream for all scales:

\[
 x:\mathbb N\to\{0,1\},\qquad x(k)=0\quad(k\ge0).          \tag{4.1}
\]

This is `constantBinaryStream : Stream (Fin 2)` in the Lean file. At every
`n>=1`, put

\[
 L_n=2^{\lfloor n/2\rfloor}.                              \tag{4.2}
\]

The required prefix consists of positions `0,...,L_n+n-2` of the single
stream (4.1). Thus the family is not a sequence of unrelated finite words.
Every length-`n` block is `0^n`, so each allowed comparison is an equality.

For `m_n=min(n-1,L_n-1)`, the exact ordered counts are

\[
 S_n=2\sum_{r=1}^{m_n}(L_n-r),                            \tag{4.3}
\]

\[
 R_n=2\sum_{r=n}^{L_n-1}(L_n-r)
    =L_n(L_n-1)-S_n.                                      \tag{4.4}
\]

An empty interval contributes zero. The factor two in both formulas is both
orientations. The declarations
`binaryExactShortPairCount_constantBinaryStream`,
`binaryExactLongPairCount_constantBinaryStream`, and
`constantRun_short_add_long` check the summation identities and the partition

\[
 S_n+R_n=L_n(L_n-1).                                      \tag{4.5}
\]

The first `L_n` block starts use symbols only through `L_n+n-2`, so (4.1) also
verifies the endpoint legality in (3.2)-(3.3).

## 5. T87 discriminator and exact finite prefix

T87 defined

\[
 D_2(n)=\max_x\frac{2S_x^=-3R_x^=}{2L_n}.                 \tag{5.1}
\]

Its exhaustive experiment found `0,1,1,3,3,41/8` for `1<=n<=6`; a maximizer
at each of those scales is the restriction of (4.1). For the constant family
itself, exact reduction of (4.3)-(4.4) gives the table below.
`verify_note.py` independently exhausts all binary words at `1<=n<=6` and
reproduces T87's maxima; this bounded calculation remains an **experiment**
and is not used in Section 6's infinite proof.

| `n` | `L_n` | `S_n` | `R_n` | `(2S_n-3R_n)/(2L_n)` |
|---:|---:|---:|---:|---:|
| 1 | 1 | 0 | 0 | 0 |
| 2 | 2 | 2 | 0 | 1 |
| 3 | 2 | 2 | 0 | 1 |
| 4 | 4 | 12 | 0 | 3 |
| 5 | 4 | 12 | 0 | 3 |
| 6 | 8 | 50 | 6 | `41/8` |
| 7 | 8 | 54 | 2 | `51/8` |
| 8 | 16 | 168 | 72 | `15/4` |
| 9 | 16 | 184 | 56 | `25/4` |
| 10 | 32 | 486 | 506 | `-273/32` |
| 11 | 32 | 530 | 462 | `-163/32` |

`constant_family_equality_at_seven` checks the `n=7` equality. These finite
values locate the sharp constant for this family, but they are not the proof
of the infinite conclusion.

## 6. Infinite uniform bound

The machine-checked conclusion is

\[
 \boxed{\forall n\ge1:\quad 8S_n\le51L_n+12R_n.}          \tag{6.1}
\]

Equivalently,

\[
 S_n\le\frac{51}{8}L_n+\frac32R_n,
 \qquad \frac{2S_n-3R_n}{2L_n}\le\frac{51}{8}.            \tag{6.2}
\]

Equality holds at `n=7`, so `51/8` is the optimal constant for this family.
The infinite proof is:

1. The positive short lags form a subset of `{1,...,n-1}` and each has at
   most `L_n` starts. Hence
   \[
   S_n\le2nL_n.                                            \tag{6.3}
   \]
   This is `constantShortCount_le_two_mul`.
2. For every `k>=6`,
   \[
   20k+10\le3(2^k-1).                                     \tag{6.4}
   \]
   At `k=6`, this is `130<=189`. In the induction step, the left side
   increases by `20`, while the right side increases by `3*2^k>=192`.
   This is `twenty_mul_add_ten_le_three_mul_two_pow_sub_one`.
3. If `n>=12` and `k=floor(n/2)`, then `k>=6` and `n<=2k+1`. Therefore
   \[
   10n\le20k+10\le3(L_n-1).                               \tag{6.5}
   \]
4. Combining (6.3), (6.5), and (4.5),
   \[
   5S_n\le10nL_n\le3L_n(L_n-1)=3(S_n+R_n),               \tag{6.6}
   \]
   so
   \[
   2S_n\le3R_n.                                           \tag{6.7}
   \]
   Thus the stronger Review-B inequality with additive constant zero holds
   for every `n>=12`. This is `late_constantShortCount_charged_by_long`.
5. The kernel reduces the exact definitions for `0<=n<=11`; the allowed
   range `1<=n<=11` is displayed above. Combining that finite base with (6.7)
   proves (6.1). The direct legal-stream theorem is
   `legal_constantBinaryStream_uniform_reviewB_bound`.

The proof uses exact identities and induction, not finite-growth
extrapolation.

## 7. Exact charging feature and surviving gap

**Candidate disposition: uniformly bounded.** The apparent growth through
`n=7` comes from the regime where `L_n` is still comparable with `n`, so most
equal pairs have short lag. It cannot continue. On a constant run, the short
load is only `O(nL_n)`, while every pair of starts has the same block label.
Once `L_n` dominates `n`, the complementary long load is quadratic:
`R_n=L_n(L_n-1)-S_n`. Equation (6.6) then charges every short pair to long
pairs with coefficient `3/2` and no additive loss.

The surviving universal gap is exact: for an arbitrary nonconstant word, no
proved argument currently turns high multiplicity among the starts within
distance `<n` into enough equal-block pairs at distances `>=n`, with at most
`C_bL` uncharged pairs and coefficient exactly `3/2`, uniformly in `n` and the
word. Review B's proposed parity-bin and short-period enumeration is still
missing that endpoint, separation, and multiplicity accounting. Any
counterexample must make

\[
 \frac{S_x^=-(3/2)R_x^=}{L}
\]

unbounded while suppressing the remote equalities that kill the constant-run
family.

This closes only the leading T87-inspired constant-run mechanism. It neither
proves `(RB)` nor transfers exact equality to T56's neighboring-cylinder and
carry-thickened strict near-return statistic.

## 8. Machine-checked declaration index

All declarations are public and lie in the fresh namespace
`DecimalFactorComplexity.T92ConstantRunDiscriminator`.

| Declaration | Content |
|---|---|
| `binaryExactShortPairCount_constantBinaryStream` | Exact short count on one legal binary stream |
| `binaryExactLongPairCount_constantBinaryStream` | Exact long count, including lag `n` |
| `constantRun_short_add_long` | Exact short/long partition |
| `constantLongCount_eq_legal_binary_stream_count` | Numerical `R_n` equals the legal-stream statistic |
| `constantShortCount_le_two_mul` | `S_n<=2nL_n` |
| `twenty_mul_add_ten_le_three_mul_two_pow_sub_one` | Explicit exponential recurrence bound |
| `late_constantShortCount_charged_by_long` | `2S_n<=3R_n` for every `n>=12` |
| `constant_family_uniform_reviewB_bound` | Denominator-free uniform `51/8` bound |
| `legal_constantBinaryStream_uniform_reviewB_bound` | Uniform bound directly on the infinite binary stream |
| `constant_family_equality_at_seven` | Sharp equality at `n=7` |

Compilation command from the repository root:

```sh
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t92-1786304634-r0/theory_artifacts/T92ConstantRunDiscriminator.lean
```

The printed dependencies are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The Lean file contains no `sorry`, `admit`, `native_decide`, new
axiom, unsafe declaration, or compiler-trusting shortcut.

## 9. Final scope

T92 proves a uniform bound for one exact-word binary family. It does not prove
Review B for arbitrary words, C7, canonical (1.2), C1, C2, positive entropy,
normality, or any fixed-pi estimate.

**No fixed-pi, C1, or C2 claim is made.**
