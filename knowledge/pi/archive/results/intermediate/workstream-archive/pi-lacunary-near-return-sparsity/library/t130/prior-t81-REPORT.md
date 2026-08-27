# T81: simultaneous T73 packing versus the irrationality measure of pi

Status: `proof sketch`.

Date: 2026-08-09 UTC.

Terminal verdict: **FALSIFICATION OF THE EXECUTED SCALAR-PACKING TEST.**

This note does not prove canonical C1, its negation, a T28 compatibility
instance, normality, or any new theorem about pi. The T73 and T28 statements
quoted below are kernel-checked in the accepted library and are vendored here
byte-for-byte for inspection. The packing derivation in this report is a
rigorous prose argument, not a Lean theorem. Reports consulted as negative
inventory are unverified notes and are not mathematical premises.

## 1. Provenance and exact target

- Canonical local source URL: `local:pi-lacunary-near-return-sparsity`.
- Original project file: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Byte-exact delivered copy: `canonical_statement.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- The local source records no external original URL. Its line 5 preserves its
  system provenance and date, 2026-07-22.
- Prize: none.

For integers `n,N>=1`, let

\[
 Q_\pi(n,N)=\#\{(i,j):0\le i,j<N,
   \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{1.1}
\]

The target called C1 in the present agenda is exactly canonical A1 in the
immutable source:

\[
 \boxed{\forall A\ge1\ \exists n_0\ge1\ \forall n\ge n_0\
 \exists N\ge1:\quad AnQ_\pi(n,N)\le N^2.}
\tag{1.2}
\]

Pairs are ordered, the diagonal is included, the circle inequality is strict,
the base is 10, and `N` may depend on `A,n`. Infinitely many depths, one fixed
`A`, prescribed `N`, omitted diagonals, unordered pairs, ordinary absolute
distance, equal decimal words, other constants, and almost-everywhere models
are sibling statements and are not substituted here.

## 2. Endpoints stated before derivation

**SUCCESS endpoint.** A source-pinned theorem about pi, applied simultaneously
to the complete legal T73 child family, must either contradict the literal
T73 consequence of `not C1` or supply the actual cross-node integer
cancellation and exponent-closing inequalities required by T28.

**FALSIFICATION endpoint.** After retaining T73's complete child set, residual
lengths, resonance windows, forbidden shift, coefficient factors, and ambient
height, an exact simultaneous uniform-height and fixed-block packing
calculation shows that the selected theorem gives only numerically vacuous
caps. Pointwise application to each child is not success.

The calculation below reaches the falsification endpoint for the specified
packing test. Its scope is the selected exponent-eight irrationality theorem
used through the displayed uniform-height and fixed-block consequences of
pairwise scalar separation. It does not prove that every multiscale or
coefficient-order-sensitive deduction from the same pairwise inequalities is
impossible, and it does not rule out a future theorem that directly controls a
simultaneous family of related decimal coefficients.

## 3. Trusted inputs and negative inventory

### 3.1 Kernel-checked interfaces

| Input | Delivered file and SHA-256 | Exact locators used |
|---|---|---|
| T73 | `T73ManyChildResonance.lean`, `34ec4af51b95e7e1e1a0a350357fedf4fb7c0427daaf8a53331c3767992727de` | `goodMiddleShifts`, lines 29-35; membership, lines 39-46; cardinality theorem, lines 63-72; child identity, lines 267-292; length threshold, lines 294-297; literal not-C1 theorem, lines 305-344 |
| T28 | `T28AdjacentNodeCompatibility.lean`, `f94c5c2060be43f0800e83adb782b5f3d20ee3fff7beadd2d28c9e92cc818dbd` | compatibility predicate, lines 88-107; exponent-eight closing bounds, lines 109-122; contradiction theorem, lines 390-451; conditional C1 bridge, lines 453-492 |

T73 proves only a necessary consequence of literal failure. T28 proves a
conditional bridge whose compatibility and closing predicates are hypotheses;
neither module asserts those predicates for pi.

### 3.2 Consulted obstruction inventory

The following accepted-library reports were consulted on 2026-08-09. They are
navigation and comparison only unless backed by the two vendored Lean files or
the primary source below.

| Item | Verification level relevant here | Boundary recorded by the note |
|---|---|---|
| T18, T21 | `proof sketch` | A scalar irrationality measure gives exponent-one approximations after coefficient growth; no contradiction. |
| T40, T43 | `proof sketch` | Abstract fixed-stratum or resonance-only phase information does not establish the actual fixed-pi aggregate criterion. |
| T46 | `proof sketch` | On one genuine T26/T38 stratum, exponent-seven pair separation leaves a non-closing packing regime. |
| T63 | `literature-checked` applicability audit | BBP/Zudilin/Bailey--Crandall sources supply no base-10 fixed-pi simultaneous cancellation estimate. |
| T68 | kernel-checked declarations, prose companion | Removing the power-of-five transient does not repair the corrected-Zudilin displayed-denominator route. |
| T78 | `proof sketch` | The factorial truncation has a route-specific denominator/order scale obstruction. |
| T79 | `proof sketch` literature audit | The retained Machin-like truncation also has a square-root-modulus scale obstruction. |

The changed evidence in T81 is not an abstract phase or a synthetic
fixed-stratum witness. It is T73's one common parent together with a
linear-size set of actual fixed-pi children, all retaining the common factor
`h*(10^r-1)` and their individual factors `10^s-1`.

## 4. Pinned theorem about pi

The selected source is Doron Zeilberger and Wadim Zudilin, *The irrationality
measure of pi is at most 7.103205334137...*, Moscow Journal of Combinatorics
and Number Theory 9 (2020), no. 4, 407--419,
DOI `10.2140/moscow.2020.9.407`.

The publisher PDF and layout extract are delivered as
`zeilberger-zudilin-2020.pdf` and `zeilberger-zudilin-2020.txt`. Their hashes
and URLs are in `SOURCE_PINS.md`. Printed p. 407, PDF page 2, extract lines
27-34 defines the irrationality measure by the eventual inequality for every
positive epsilon and all integer numerators. Printed p. 418, PDF page 13,
extract lines 676-691 gives

\[
 \mu(\pi)\le 7.10320533413700172750577342281\ldots<36/5.
\tag{4.1}
\]

Choose epsilon `4/5` in the definition. There is therefore an existential
integer `Q8>=1`, not numerically specified by the source, such that

\[
 \boxed{q\ge Q_8,\ p\in\mathbb Z
 \quad\Longrightarrow\quad |\pi-p/q|>q^{-8}.}
\tag{4.2}
\]

Choosing a nearest integer to `q*pi` and multiplying by `q` gives the exact
scalar consequence

\[
 \boxed{q\ge Q_8\quad\Longrightarrow\quad
 \|q\pi\|_{\mathbb R/\mathbb Z}>q^{-7}.}
\tag{4.3}
\]

No explicit value of `Q8` is asserted. This is the strongest explicit
pi theorem used in this note; no claim of an exhaustive global record search
beyond the accepted source audit is made.

## 5. Full T73 specialization

Temporarily assume the literal negation of (1.2). The vendored T73 theorem,
lines 305-344, gives

\[
 \exists A\ge1\ \forall n_0\ge1\ \exists n\ge n_0,
 \quad n\ge1,
\tag{5.1}
\]

and, after `A,n` are fixed, for every requested `K>=1` children and every
requested residual threshold `R>=1`, integers `N,r,h` with the following exact
data. Put

\[
 D:=131072A^2n^2,\qquad E:=8D^2,\qquad H:=256An.
\tag{5.2}
\]

The ambient length and parent parameters are

\[
 \boxed{N=16An\,E(K+R+3)=128AnD^2(K+R+3),}
\tag{5.3}
\]

\[
 1\le r\le N-1,\qquad 1\le h\le H.
\tag{5.4}
\]

Set `M=N-r`. The specialized good-child set is exactly

\[
 \begin{aligned}
 G=\{s:\;&1\le s\le M-R,\ s\ne r,\\
 &L_s/E<\Re\sum_{0\le j<L_s}
 e(q_{s,j}\pi)\},
 \end{aligned}
\tag{5.5}
\]

where

\[
 L_s:=N-r-s=M-s,
\qquad
 q_{s,j}:=h(10^r-1)(10^s-1)10^j,
\tag{5.6}
\]

and `e(x)=exp(2*pi*i*x)`. Every child has

\[
 1\le s\le N-r-R,\quad s\ne r,\quad L_s\ge R,
\tag{5.7}
\]

and T73 guarantees

\[
 \boxed{K\le |G|.}
\tag{5.8}
\]

For completeness, the generic kernel-checked cardinality theorem says

\[
 {3M\over8D^2}-{1\over2}-(B+|F|+R)<|G|.
\tag{5.9}
\]

Here `B=1` and `F={r}`, so the complete specialized losses are

\[
 \boxed{{3M\over E}-R-{5\over2}<|G|.}
\tag{5.10}
\]

The terms in (5.10) are respectively the main autocorrelation mass, diagonal
loss `1/2`, one short-shift loss, one forbidden-shift loss, and the terminal
loss `R`. There is no hidden floor or ceiling. Equations (5.8) and (5.10) are
the two cardinality facts used below; no omitted internal length property is
inferred from T73's proof.

## 6. Every child supplies a positive-cosine window

For every `s in G`, define

\[
 J_s:=\{j:0\le j<L_s,\ \cos(2\pi q_{s,j}\pi)>0\}.
\tag{6.1}
\]

Each cosine is at most one, and every summand outside `J_s` is nonpositive.
Taking real parts in (5.5) therefore gives

\[
 {L_s\over E}<\sum_{j<L_s}\cos(2\pi q_{s,j}\pi)
 \le |J_s|.
\tag{6.2}
\]

The positivity window is exact:

\[
 \cos(2\pi x)>0
 \quad\Longleftrightarrow\quad
 \|x\|_{\mathbb R/\mathbb Z}<1/4.
\tag{6.3}
\]

Thus all selected phases lie in the same open half-circle and

\[
 |J_s|>{L_s\over E}\ge {R\over E}.
\tag{6.4}
\]

Let the complete positive-window family be

\[
 \mathcal P:=\{(s,j):s\in G,\ j\in J_s\},\qquad P:=|\mathcal P|.
\tag{6.5}
\]

Summing (6.4) simultaneously over every legal child gives the strict lower
bound

\[
 \boxed{P=\sum_{s\in G}|J_s|>{1\over E}\sum_{s\in G}L_s
 \ge {|G|R\over E}\ge {KR\over E}.}
\tag{6.6}
\]

Combining the same count with (5.10) also retains the raw cardinality estimate:

\[
 P>{R\over E}\left({3M\over E}-R-{5\over2}\right).
\tag{6.7}
\]

Equation (6.6), rather than an arbitrary `K`-element subfamily, is the
simultaneous use of the complete legal family. It is stronger than choosing
one unspecified phase from each child.

## 7. Coefficient injectivity and complete height

Write `C=h*(10^r-1)>0`. If two coefficients in (5.6) are equal, cancellation
of `C` gives

\[
 10^j(10^s-1)=10^{j'}(10^{s'}-1).
\tag{7.1}
\]

Because every `10^s-1` is odd, the 2-adic valuation of the left side is
exactly `j`. Hence `j=j'`, after which strict monotonicity of `10^s-1` gives
`s=s'`. Therefore

\[
 \boxed{(s,j)\mapsto q_{s,j}\text{ is injective}.}
\tag{7.2}
\]

No collision loss is hidden in `P`.

For `j in J_s`, the range `j<L_s=N-r-s` gives

\[
 r+j+s\le N-1.
\tag{7.3}
\]

Retaining all coefficient factors and using (5.4),

\[
 \begin{aligned}
 q_{s,j}
 &=h(10^r-1)(10^s-1)10^j\\
 &<h10^{r+s+j}\le h10^{N-1}\le H10^{N-1}.
 \end{aligned}
\tag{7.4}
\]

Define the integer height

\[
 \boxed{Q:=H10^{N-1}=256An\,10^{N-1}.}
\tag{7.5}
\]

All `P` coefficients are distinct positive integers strictly below `Q`.

## 8. Simultaneous irrationality packing

For each coefficient in `mathcal P`, choose its unique representative

\[
 y_q\in(-1/4,1/4),\qquad y_q\equiv q\pi\pmod1,
\tag{8.1}
\]

which exists by (6.3).

The source theorem applies only to differences at least `Q8`. Sort the `P`
distinct integer coefficients and greedily retain the least remaining one,
then discard all later coefficients less than `Q8` above it. Each retained
coefficient removes at most `Q8` integer values. The retained set `T` therefore
satisfies

\[
 P\le Q_8|T|,
\qquad |q-q'|\ge Q_8\quad(q\ne q',\ q,q'\in T).
\tag{8.2}
\]

For distinct `q,q' in T`, put `d=|q-q'|`. Since `q,q'<Q`,
`Q8<=d<Q`. Equations (4.3) and (8.1) imply

\[
 \|y_q-y_{q'}\|_{\mathbb R/\mathbb Z}
 =\|d\pi\|_{\mathbb R/\mathbb Z}
 >d^{-7}>Q^{-7}.
\tag{8.3}
\]

All representatives lie in one interval of length `1/2`. Ordering them by
their real value and summing the adjacent gaps gives

\[
 (|T|-1)Q^{-7}<1/2,
\qquad |T|<1+{Q^7\over2}.
\tag{8.4}
\]

Combining (6.6), (8.2), and (8.4) yields the complete output of the displayed
uniform-height thinning-and-packing deduction:

\[
 \boxed{{KR\over E}<P<Q_8\left(1+{Q^7\over2}\right).}
\tag{8.5}
\]

There is no pointwise-to-simultaneous promotion hidden here: (8.3) was applied
to every retained pair, and (8.4) packs the entire retained family at once.

One can localize the same argument. Partition `[1,Q)` into coefficient blocks
of width `W>=Q8`, thin within each block as above, and pack using separation
`>W^(-7)`. With `B_W=ceil((Q-1)/W)`, this gives

\[
 P<Q_8B_W\left(1+{W^7\over2}\right).
\tag{8.6}
\]

Taking fixed `W` improves this global exponent-seven cap to a constant times
`Q`, but not to a quantity polynomial in `N`. Independently, injectivity alone
already gives the sharper elementary bound `P<=Q-1`. Thus neither of the two
executed packing scales overcomes the exponential coefficient height. No claim
is made here that (8.5)-(8.6) optimize every possible multiscale use of all
distance-dependent inequalities `d^(-7)`.

## 9. Complete height and exponent comparison

Substitute (5.2), (5.3), and (7.5):

\[
 E=8(131072A^2n^2)^2,
\tag{9.1}
\]

\[
 N=128An(131072A^2n^2)^2(K+R+3),
\tag{9.2}
\]

\[
 Q=256An\,10^{128An(131072A^2n^2)^2(K+R+3)-1}.
\tag{9.3}
\]

The scalar theorem has exponent eight for `|pi-p/q|`, hence exponent seven
for circle separation and the `Q^7` global capacity in (8.5). T73 guarantees
the complete-family lower bounds (6.6)-(6.7), including `|G|R/E>=KR/E`.
The comparison with the parameter-only lower term is not asymptotic shorthand:
for all legal `A,n,K,R`,

\[
 N\ge128(K+R+3),\qquad Q\ge10^{K+R+2}.
\tag{9.4}
\]

For every positive integer `m`, `m<=2^m`; hence

\[
 {KR\over E}\le KR\le2^{K+R}
 <{10^{7(K+R+2)}\over2}
 \le {Q^7\over2}
 \le Q_8{Q^7\over2}.
\tag{9.5}
\]

Thus the lower population required by T73 is strictly below even the dominant
term of the scalar packing allowance for every legal parameter choice. Taking
`K` and `R` larger worsens the comparison because `N`, and therefore `Q`, is
already exponential in `K+R` after the decimal power in (9.3). The localized
or trivial injective cap is also non-closing:

\[
 {KR\over E}\le KR<10^{K+R+2}\le Q.
\tag{9.6}
\]

Equations (8.5), (9.3), and (9.5) are the requested complete packing,
coefficient-height, and exponent comparison. The theorem does not force a
contradiction to T73 through the executed packing test.

This conclusion retains all of `G`, not only its guaranteed `K` children. The
range in (5.5) gives `|G|<=M`, and every `L_s<=M`, so

\[
 P\le\sum_{s\in G}L_s\le M|G|\le M^2\le N^2<Q.
\tag{9.7}
\]

The last inequality holds because (9.2) gives `N>=128*5` and
`Q>=10^(N-1)>N^2`. Thus even the maximum possible population of the complete
T73 window family remains below the elementary coefficient-height scale.

## 10. Why this does not bridge T28

T28's `AdjacentPairCompatible`, vendored lines 91-107, requires two specific
eventually-periodic integer approximants with errors `e0,e1` satisfying

\[
 Q_0e_1+UQ_1e_0<1.
\tag{10.1}
\]

This strict budget forces exact cross multiplication of the two numerators.
T28's `ExponentEightClosingBounds`, lines 111-122, additionally requires a
bounded denominator `q<=qCap`, `q>=Q8`, and

\[
 e_0(q_{\rm cap})^8<CQ_0.
\tag{10.2}
\]

T73 plus the positive-cosine extraction gives only the individual upper
window

\[
 \|q_{s,j}\pi\|<1/4,
\tag{10.3}
\]

while the source theorem gives the lower bound

\[
 \|q_{s,j}\pi\|>q_{s,j}^{-7}
\quad\text{when }q_{s,j}\ge Q_8.
\tag{10.4}
\]

Neither inequality relates two selected integer numerators, forces (10.1),
bounds T28's preperiod and period data, or makes the eighth-power expression
(10.2) small. A lower irrationality bound cannot manufacture the missing
upper error or exact cancellation. Consequently T28's accepted conditional
frontier remains uninstantiated.

## 11. Terminal obstruction

\[
\boxed{\begin{minipage}{0.91\linewidth}
T73's literal not-C1 consequence gives the complete genuine child set `G` and,
after retaining every resonance window, more than `|G|R/E>=KR/E` distinct
coefficients `h(10^r-1)(10^s-1)10^j` in one positive half-circle. Applying the
pinned exponent-eight theorem simultaneously to all eligible coefficient
differences through the displayed uniform-height test gives only the packing
cap (8.5), while the fixed-block test gives (8.6). The exact T73 height is
`Q=256An*10^(N-1)` with `N=128AnD^2(K+R+3)`, so the scalar capacity is
exponential in `K+R` and (9.5) is automatically compatible with the T73 lower
count for every legal parameter choice. The same data provide none of T28's
cross-numerator cancellation or eighth-power closing budget. Therefore this
irrationality-measure theorem, under the executed simultaneous
uniform-height/fixed-block packing test, collapses to insufficient scalar
information and does not bridge T73 to T28.
\end{minipage}}
\tag{11.1}
\]

This is a displayed quantitative obstruction to the selected test, not a
claim that every multiscale consequence of scalar irrationality has been
classified. A theorem capable of success must control the related family at a
scale polynomial in the residual data, directly force T28's cross
multiplication, or provide a genuinely stronger coefficient-sensitive packing
bound than (8.5)-(8.6). No such estimate is treated as established here.

## 12. Verification and non-claims

Run from a directory containing only the delivered artifacts:

```bash
python3 verify_note.py
```

The script checks all vendored hashes and exact source/interface anchors. It
also performs finite exact-integer sanity checks of coefficient injectivity,
T73's height inequality, parameter expansion, and the automatic comparison
(9.5). Those finite checks audit transcription only and are not evidence for
the universal prose argument.

The adversarial verification pass on 2026-08-09 additionally completed
`lake build TheoryLib` and one sequential direct compile of each vendored Lean
file:

```bash
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t81-1786279777-r2/theory_artifacts/T73ManyChildResonance.lean
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t81-1786279777-r2/theory_artifacts/T28AdjacentNodeCompatibility.lean
```

T73 compiled without warnings. T28 compiled with three style-only
`unnecessarySimpa` warnings. Every printed theorem axiom set contained exactly
`propext`, `Classical.choice`, and `Quot.sound`. Concurrent preliminary compile
attempts were cut off by the runtime timeout without Lean diagnostics; no such
attempt is counted as verification.

The same pass reopened the DOI and publisher records, visually/textually
checked printed pp. 407, 417, and 418 in the delivered PDF, and reran
`pdftotext -layout` from the PDF. The fresh extract had SHA-256
`49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`
and was byte-identical to the delivered extract.

- Lean statement added by T81: none.
- New machine-checked theorem claimed by T81: none.
- Canonical C1 proved or disproved: no.
- T28 compatibility proved for pi: no.
- Literature status: the selected primary source is byte-pinned; the broader
  inventory statuses remain exactly as listed in Section 3.
- Independent statement, proof, and novelty review: pending.
