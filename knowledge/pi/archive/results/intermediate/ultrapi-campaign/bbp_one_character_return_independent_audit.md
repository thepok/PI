# Independent audit: BBP one-character return

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local question has no external source URL; none is invented.

Audited primary artifacts:

- [bbp_one_character_return_attack.md](bbp_one_character_return_attack.md),
  SHA-256
  `b49bfb3793dd87abf7b5dedaa820c87dfcf23ab3856e9fa67ef2462fbefecfab`;
- [bbp_one_character_return_check.py](bbp_one_character_return_check.py),
  SHA-256
  `4d4cf5933f0d9751ea84fffaf2a7f1e25c84769e50e3e77b1b4083982a660372`.

Independent replay:

- [bbp_one_character_return_independent_check.py](bbp_one_character_return_independent_check.py),
  SHA-256
  `75286116c6472445d40ba648696babea8ead2e90be8fe67b586c1e9ee107d577`.

## Verdict

**PASS with no correction to either primary artifact.**

The exact rational identities, analytic inequalities, source hypotheses,
quantifiers, and source pins rederive.  The primary conclusions retain status
`proof sketch`; the bounded source audit is `literature-checked` on the audit
date; both finite replays are only `experiment`.  T69 is `machine-checked` for
its conditional reduction only.  No fixed-sixteen return and no V1 statement
is proved.  Canonical V1 remains a `conjecture`.

The exact remaining blocker is unchanged:

\[
 \liminf_{n\to\infty}\|(10^n-16)B_n\|_{\mathbb T}=0,
 \qquad
 B_n=\sum_{k=0}^n{a(k)\over16^k},
\]

or, equivalently, the four-pole-specific recurrence must satisfy

\[
 \limsup_{n\to\infty}\Re Z_n=1.
\]

Neither the Chen--Ye--Zheng dispersion theorem, the Fejer alternative, the
triangular reindexing, nor finite replay establishes this return.

## 1. Normalization and the exact T69 dependency

The normalized target is precisely the list-valued V1 statement: every finite
word over \(\{0,\ldots,9\}\), including words with leading zeroes and the empty
word, occurs contiguously in the decimal expansion of pi.  The two recorded
noncanonical readings remain distinct: an arbitrary infinite word cannot all
occur as a tail, while arbitrary infinite subsequences amount to every digit
occurring infinitely often.

T69 defines the fixed return as

\[
 16(\pi\bmod1)\in
 \overline{\{10^n\pi\bmod1:n\in\mathbb N\}}
\]

and proves the exact conditional theorem

\[
 \operatorname{Dense}\{10^s16^t\pi\bmod1:s,t\in\mathbb N\}
 \Longrightarrow (\mathrm{V1}\leftrightarrow\mathrm{R16}).       \tag{A1}
\]

The density premise in (A1) is exactly the one used by T69.  No
zero-accumulation field, invariant-set dichotomy, or stronger packaged premise
is hidden in the theorem.  The T69 module hash is
`fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9`;
its report hash is
`7094e4b4da2747b6e6f7ec4dc7c2390d4104f852f476098d8c6f9a3983fa8bf6`;
and its prior independent-audit hash is
`99dfa03eff652fba1dcfa3f21a2eae24d484bc611148af7b975d035a32ea0255`.

Furstenberg's Theorem IV.1 supplies the displayed density on paper.  Its
Definition IV.1 says that an integer semigroup is lacunary exactly when all
positive members are powers of one integer.  The semigroup containing 10 and
16 is nonlacunary, since those two integers cannot be powers of one common
integer, and pi is irrational.  This paper step is source-audited, not inserted
into Lean as an axiom.

For completeness, the passage from T69's closure quantifier to the primary
report's liminf is exact.  Circle distance gives

\[
 d_{\mathbb T}(16\pi,10^n\pi)=\|(10^n-16)\pi\|_{\mathbb T}.
\]

No one of these distances is zero: \(10^n-16\ne0\) and pi is irrational.
Therefore an arbitrarily accurate closure hit cannot be confined to a finite
set of indices.  It yields an unbounded sequence of indices and hence liminf
zero.  The converse is immediate.  Thus the equivalence used in the primary
report is exactly T69 plus its audited Furstenberg density premise and the
elementary no-exact-hit observation; it is not an unconditional Lean theorem.

## 2. BBP tail, rational recurrence, and one character

The standard BBP summand combines exactly as

\[
 {4\over8k+1}-{2\over8k+4}-{1\over8k+5}-{1\over8k+6}
 ={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}=a(k).                    \tag{A2}
\]

It is positive.  For \(k\ge1\), direct expansion gives

\[
\begin{aligned}
 &(2k+1)(4k+3)(8k+1)(8k+5)
   -k^2(120k^2+151k+47)\\
 &\qquad=392k^4+873k^3+665k^2+194k+15>0.
\end{aligned}
\]

Hence \(a(k)<k^{-2}\), and the positive tail is

\[
 0<\pi-B_n
 <{1\over(n+1)^2}\sum_{k=n+1}^{\infty}16^{-k}
 ={16^{-n}\over15(n+1)^2}.                          \tag{A3}
\]

The primary weak inequality is therefore valid with the claimed constant
\(1/15\).  For \(n\ge2\), multiplication by
\(q_n=10^n-16\in(0,10^n)\) gives its stated
\((5/8)^n/(15(n+1)^2)\) transfer bound.

With \(b_n=a(n)/16^n\), the two identities

\[
 B_{n+1}=B_n+b_{n+1},\qquad q_{n+1}=10q_n+144
\]

give, without approximation,

\[
 R_{n+1}=10R_n+144B_n+q_{n+1}b_{n+1}.
\]

Applying \(e(x)=\exp(2\pi ix)\) gives the displayed recurrence for
\((V_n,Z_n)\).  All its exponents are rational, so both coordinates are roots
of unity; \(B_0=47/15\), \(R_0=-47\), and hence \(Z_0=1\).

Finally, if \(d=\|x\|_{\mathbb T}\in[0,1/2]\), then

\[
 1-\Re e(x)=2\sin^2(\pi d).
\]

On this interval the right side tends to zero exactly when \(d\) tends to
zero.  Consequently the liminf return is equivalent to
\(\limsup\Re Z_n=1\).  This is a pointwise one-character equivalence; it does
not assert a Cesaro limit or a Weyl criterion.

## 3. Full triangle, tent weights, error, and carry arc

For a fixed column \(n\), membership in the triangle is exactly

\[
 \max(5,c(n))\le M\le\min(n,K),
 \qquad c(n)=\min\{M:10^n\le16^M\}.
\]

Its cardinality is therefore

\[
 w_K(n)=\max(0,\min(n,K)-\max(5,c(n))+1),
\]

which proves the reindexing and the stated range \(5\le n\le L_K\).

For each triangular pair, positivity and (A3) give

\[
 0<(10^n-16)(\pi-B_M)
 <{10^n16^{-M}\over15(M+1)^2}
 \le {1\over15(M+1)^2}.                              \tag{A4}
\]

Using \(|e(u)-e(v)|\le2\pi|u-v|\) proves the complete right side of
the primary equation (15d).  Also
\(L_M\le2M-1\), so its numerator is
\(O(\sum_{M\le K}M/(M+1)^2)=O(\log K)\).  Since
\(L_M\ge\lfloor6M/5\rfloor\), each late row has at least order \(M\)
entries and \(N_K\gg K^2\).  Thus the normalized error really is
\(O_h(\log K/K^2)\) for each fixed integer \(h\).

For admissible \(M_0<M_1\) in one column,

\[
 0<(10^n-16)(B_{M_1}-B_{M_0})
 <(10^n-16)(\pi-B_{M_0})
 \le {1\over15(M_0+1)^2}.                            \tag{A5}
\]

Thus the copies are genuinely confined to one shrinking unwrapped arc.  The
triangle supplies multiplicity, not a second independent phase family.  A
weighted Fejer argument may select a low mode along a subsequence, but no
triangle identity rules that mode out.

## 4. Chen--Ye--Zheng: hypotheses and exact quantifiers

The current arXiv record on 2026-08-13 lists only v1, submitted 2026-04-15.
Definition 1.2 and Theorem 1.3 on PDF page 2 were checked against the pinned
PDF, the arXiv HTML, and the fetched v1 e-print source.

The source assumes a nonzero \(R\in\mathbb Z[T]\), a real sequence satisfying
its recurrence for all \(k\ge1\), and a representation
\(x_k=\sum_iF_i(k)\alpha_i^k\) with distinct \(\alpha_i\).  Here

\[
 R=P=(T-10)(T-1),\quad
 (\alpha_1,\alpha_2)=(10,1),\quad
 (F_1,F_2)=(\pi,-16\pi).
\]

Condition \((c')\), stated by the source as a sufficient case of condition
\((c)\), holds because \(|10|>1\) and
\(\pi\notin\mathbb Q(10)[T]=\mathbb Q[T]\).  It therefore triggers all three
main conclusions of Theorem 1.3: an infinite limit set, the \(L(R)\) limsup
bound, and the \(\lambda(R)\) progression-spread conclusion.  It is not the
weaker condition \((e)\), for which the source retains only infinitude.

The progression quantifiers are exactly

\[
 \forall M\ge1\ \exists l\ge0:
 E_{M,l}\text{ is not contained in any circle interval of length }
 <1/\lambda(R),                                      \tag{A6}
\]

where \(E_{M,l}\) is the limit set of
\((x_{kM+l})_{k\ge1}\).  The residue \(l\) may depend on \(M\).  Replacing it
by \(l\bmod M\) changes only finitely many initial terms and hence not the
limit set.  The source does not give one common residue for every modulus.

## 5. The constants 22 and 10 are optimal only at this interface

The displayed recurrence has \(L(P)=1+11+10=22\).  To rule out a better
integer recurrence polynomial, let nonzero
\(U(T)=\sum_i u_iT^i\) annihilate \(X_n=\pi10^n-16\pi\).  Relations at two
successive indices give

\[
 10^nU(10)-16U(1)=0,
 \qquad10^{n+1}U(10)-16U(1)=0,
\]

so \(U(10)=U(1)=0\) and \(P\mid U\).  The equation \(U(1)=0\) makes the
positive and negative coefficient masses equal to an integer
\(m=L(U)/2\).  The equation \(U(10)=0\) is an equality between two multisets
of \(m\) nonnegative powers of ten.

If \(m\le10\), inspect the number of copies at the least occurring exponent.
The two counts are congruent modulo ten.  Counts between zero and \(m\) must
be equal, except possibly \(0\) and \(10\).  In that exceptional case one
side already uses all ten terms at the least exponent and has value
\(10^{r+1}\), while all ten terms on the other side are at least
\(10^{r+1}\), an impossibility.  Thus the counts agree.  Remove the common
least-exponent copies and iterate.  The two multisets coincide, so the
relation is zero.  Hence a nonzero relation has \(m\ge11\), or
\(L(U)\ge22\).  The polynomial \(P\) attains equality through
\(100+10=11\cdot10\).

For the overreduced length, the only admissible nonunit root factor of \(P\)
is \(T-1\).  Thus the candidates are \(\ell(P)\) and \(\ell(T-10)\).  Each has
Mahler measure ten.  A real multiplier with leading coefficient one or
constant coefficient one has Mahler measure at least one; Mahler measure is
multiplicative and coefficient length dominates it.  Both candidates are
therefore at least ten.  Conversely,

\[
 Q_d(T)=\sum_{j=0}^d{T^j\over10^j},\qquad
 (T-10)Q_d(T)={T^{d+1}\over10^d}-10
\]

has constant coefficient one and length \(10+10^{-d}\).  Hence
\(\lambda(P)=10\).

No other integer annihilator improves this \(\lambda\)-interface.  Every such
annihilator has the root 10.  An admissible factor removed in Definition 1.2
cannot contain that root, so the integer quotient still has root 10 and
Mahler measure at least ten.  Therefore its reduced length is at least ten.
These arguments justify the primary report's interface-optimality language;
they do not claim globally sharp orbit dispersion.

## 6. Limit-set transfer and the Fejer alternative

The BBP error gives \(d_{\mathbb T}(X_n,R_n)\to0\).  For every fixed
\(M\ge1\) and \(l\ge0\), the same is true at indices \(kM+l\).  Compactness of
the circle then proves equality of the two subsequential limit sets in both
directions.  Continuity of circle norm also transfers the limsup.  Thus the
Chen--Ye--Zheng conclusions transfer from \(X\) to \(R\) with their exact
progression quantifiers.

If the return fails, there are \(0<\delta\le1/2\) and \(n_0\) such that
\(\|R_n\|_{\mathbb T}\ge\delta\) for all \(n\ge n_0\).  The normalized Fejer
kernel satisfies

\[
 \Phi_H(x)=1+2\Re\sum_{h=1}^{H-1}(1-h/H)e(hx)
 \le {1\over H\sin^2(\pi\delta)}
\]

on this gap.  With
\(H=\lceil2/\sin^2(\pi\delta)\rceil\), the upper bound \(U\) is at most
\(1/2\).  Averaging any \(N\) late terms and using

\[
 2\sum_{h=1}^{H-1}(1-h/H)=H-1
\]

forces some \(1\le h<H\) to satisfy

\[
 \Re A_N(h)\le-{1-U\over H-1}
 \le-{1\over2(H-1)}.
\]

Only finitely many modes are available, so one fixed mode works along an
unbounded subsequence of \(N\).  The quantifier and constant in the primary
report are exact.

For every fixed \(r\ge0\),

\[
 q_{n+r}=10^rq_n+16(10^r-1),
\]

which rotates the \(h\)-average into the \(10^rh\)-average.  Shifting two
length-\(N\) index windows changes their averages by at most \(2r/N\).
Termwise BBP error has vanishing Cesaro mean, so the same magnitude
propagation holds for \(R_n\).  What propagates is nonzero magnitude for each
fixed ray step, not the original negative sign; the primary report states
this correctly.

## 7. Kempner separator and source attribution

For

\[
 \kappa=\sum_{j\ge0}10^{-2^j},
\]

Kempner's 1916 theorem specializes with base 10 and all coefficients one to
give transcendence.  Shallit's Theorem 3 proves irrationality, and Theorems
8--9 show that, after the initial zero, the decimal specialization has partial
quotients only in \(\{8,9,10,12\}\).  Bounded partial quotients make
\(\kappa\) badly approximable; Dirichlet's lower bound together with bad
approximability gives irrationality exponent exactly two.

The elementary separator bounds are also exact.  Its decimal digits are zero
or one, so every tail \(x=\{10^n\kappa\}\) lies in \([0,1/9]\).  Moreover

\[
 {11\over100}<\kappa<{1\over9},\qquad
 {16\kappa}=16\kappa-1\in(19/25,7/9).
\]

The direct gap is greater than
\(19/25-1/9>2/9\), and the wraparound gap is greater than
\(1-7/9=2/9\).  Hence

\[
 \|(10^n-16)\kappa\|_{\mathbb T}>2/9
 \quad(n\ge0).
\]

For the rational truncation
\(C_n=\lfloor10^{3n}\kappa\rfloor/10^{3n}\), comparison with a decimal tail
of all ones gives

\[
 0<\kappa-C_n\le10^{-3n}/9,
 \qquad |(10^n-16)(\kappa-C_n)|<10^{-2n}/9.
\]

Substitution into \(S_n=(10^n-16)C_n\) gives the primary recurrence and

\[
 |H_{n+1}-144\kappa|
 \le16\,10^{-3n}+10^{1-2n}/9.
\]

Thus the separator really preserves rational root-of-unity shadows, positive
rational forcing, exponential convergence, transcendence, and irrationality
exponent two while uniformly failing the return.  It deliberately does not
preserve the four-pole coefficient formula, so it identifies a limitation of
generic recurrence architecture rather than a counterexample to the target.

## 8. Source pins, search boundary, and checker coverage

The source bytes replayed as follows:

| source | SHA-256 |
|---|---|
| Furstenberg 1967 local PDF | `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358` |
| Bailey--Borwein--Plouffe local PDF | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Lagarias v2 local PDF | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56d8c308209b9` |
| Chen--Ye--Zheng v1 local and freshly fetched PDF | `a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d` |
| Chen--Ye--Zheng freshly fetched v1 e-print | `8793096b3e8e45bd9646c460e37290f39bd11a57ba9c74c8239620f22f7a45ed` |
| Shallit 1979 local PDF | `592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981` |
| Kempner 1916 local PDF | `99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014` |

The primary report's four displayed general-search queries were replayed on
2026-08-13 UTC.  They returned BBP computation sources, metric or
almost-everywhere lacunary results, and generic fractional-part literature,
not a theorem forcing a prescribed return for this fixed pi orbit.  A direct
arXiv identifier audit confirmed the current v1 metadata and exact Theorem
1.3 text.  This supports the report's dated, bounded `literature-checked`
label; it is not an exhaustive novelty claim.

The primary checker passed at depth 160 with its retained output.  It pins the
target and five directly used local PDFs and checks the finite rational
recurrences, triangle enumeration, and rational separator shadows.  It does
not pin the indirect T69/Furstenberg dependency or the remote e-print, and it
does not claim to prove limits or source theorems.

The independent checker imports no primary checker.  It pins 12 local
artifacts, including the primary report/checker, T69 module/report/audit, and
Furstenberg PDF.  It independently recombines the four BBP poles; checks the
tail polynomial, rational and torus recurrences, frequency shifts, triangle
weights and carry spans; enumerates finite base-ten multiset diagnostics;
checks the \(Q_d\) telescoping witnesses and Fejer convolution coefficients;
and replays the rational Kempner shadows.  Its depth-160 output was:

```text
status: PASS
claim_label: experiment
pinned_artifacts: 12
coefficient_identity_checks: 161
tail_majorant_checks: 160
scalar_recurrence_checks: 160
torus_recurrence_checks: 320
frequency_shift_checks: 805
linear_recurrence_checks: 159
multiset_uniqueness_checks: 19447
reduced_length_witness_checks: 21
triangular_reindex_checks: 4
triangular_pair_checks: 3640
triangular_carry_span_checks: 334
largest_triangle_size: 2707
fejer_coefficient_checks: 1023
separator_shadow_checks: 160
separator_recurrence_checks: 159
asserts_fixed_return: false
asserts_v1: false
all independent exact checks passed
```

These finite counts are an `experiment`, not proof of any asymptotic or
return.  The source theorem, Mahler-measure lower bounds, infinite
limit-set transfer, Fejer limiting pigeonhole step, and Kempner/Shallit
attributions were audited mathematically and against sources rather than
delegated to finite replay.

## Sharp handoff

The branch has correctly reduced the unresolved question to one explicit
four-pole rational recurrence and has proved unconditional dispersion in the
opposite direction.  The next valid advance must rule out every persistent
low-mode Fejer bias for that coefficient sequence, or exhibit a direct
four-pole return identity.  Generic root-of-unity dynamics, finite
irrationality exponent, triangular multiplicity, and the cited recurrence
limit-set theorem are insufficient.  No fixed-return or V1 conclusion is
available from the audited material.
