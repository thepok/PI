# T126: the reduced H1 coefficient orbit

Status: `proof sketch`. The source statement in Section 2 is
`literature-checked` against the pinned primary PDF. All deductions are
reconstructed here and do not use the T124 note as a premise. The replay is
an `experiment`: it checks finite instances and hashes, not the universal
arguments. This report makes no fixed-pi, C1, or C2 claim.

Audit date: 2026-08-10 UTC.

## 1. Provenance, normalized scope, and ambiguities

Original source URL for the canonical question: none. The question was
formulated locally by this program on 2026-07-22. Its byte-exact copy is
`canonical_statement.txt`, SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks whether, for

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\},
\]

with ordered pairs and the diagonal included, every integer `A>=1` has an
`n_0` such that every `n>=n_0` admits an `N>=1` with
`A n Q_pi(n,N)<=N^2`. The point, base, metric cutoff, and quantifier order are
not changed here. T126 studies a rational coefficient model, hence an A13/A14
sibling mechanism only.

The following ambiguities are fixed before calculation.

1. The H1 coefficient index is `n`; decimal time is `j`. They are never
   conflated.
2. The cleared coefficient orbit `n -> U_n mod 10^m` is different from the
   decimal orbit `j -> 10^j a_n mod 1` of one coefficient. The agenda's
   request for reduced moduli after powers of 10 selects the latter. The
   former is used only to derive `U_n` and its valuations.
3. A reduced modulus means the denominator after taking the fraction to
   lowest terms. An unreduced hypergeometric denominator is not used as an
   orbit modulus.
4. Occupancy always means the number of decimal-time indices in each exact
   rational residue. The collision statistic is ordered and includes all
   diagonal pairs.
5. Logarithmic depth is measured against the actual reduced denominator
   `q_n`, not the unreduced `36^n(n!)^2`.
6. Exact rational equality is not circle proximity for pi and is not a
   decimal-cylinder estimate. A separate transfer premise is stated in
   Section 9 and is unproved.

## 2. Source-pinned recurrence, reconstructed

The only primary source used for H1 is S1:

Sandip Singh and T. N. Venkataramana, "Arithmeticity of Certain Symplectic
Hypergeometric Groups," arXiv:1208.6460v2,
https://arxiv.org/pdf/1208.6460v2, SHA-256
`edc121df43a7921658c4e5ab4d728ad3021de746f9712ba5f92db933d0b0c1b3`.
On arXiv/PDF page 1 it defines, with `theta=z d/dz`,

\[
 D=\prod_i(\theta+\beta_i-1)-z\prod_i(\theta+\alpha_i).
 \tag{2.1}
\]

This source pins the operator, not the specialized recurrence. Set
`alpha=(1/6,5/6)` and `beta=(1,1)`. Then

\[
 \mathcal L=\theta^2-z(\theta+1/6)(\theta+5/6).
 \tag{2.2}
\]

For `F(z)=sum_(n>=0) a_n z^n` with `a_0=1`, comparison of the coefficient of
`z^n` in `mathcal L F=0` gives, for every `n>=1`,

\[
 n^2a_n=(n-5/6)(n-1/6)a_{n-1},
\]

or equivalently

\[
 \boxed{36n^2a_n=(6n-5)(6n-1)a_{n-1}.}                  \tag{2.3}
\]

Iteration, with no input from T124, gives

\[
 a_n={U_n\over36^n(n!)^2},\qquad
 \boxed{U_n=\prod_{k=1}^n(6k-5)(6k-1)},\quad U_0=1.     \tag{2.4}
\]

Thus `U_n` is the product of the positive integers at most `6n` that are
coprime to 6.

## 3. Every prime valuation

Each factor in (2.4) is odd and prime to 3, so

\[
 \boxed{v_2(U_n)=v_3(U_n)=0.}                            \tag{3.1}
\]

Let `p>=5` be prime and `q=p^a`. Define `r_1(q),r_5(q)` in
`{1,...,q}` by

\[
 6r_1(q)\equiv1\pmod q,\qquad6r_5(q)\equiv5\pmod q.
\]

The representatives are explicit:

\[
(r_1(q),r_5(q))=
\begin{cases}
((5q+1)/6,(q+5)/6),&q\equiv1\pmod6,\\
((q+1)/6,(5q+5)/6),&q\equiv5\pmod6.
\end{cases}                                               \tag{3.2}
\]

In either case `r_1(q)+r_5(q)=q+1`. The number of `k` in `[1,n]`
congruent to `r` modulo `q` is `floor((n+q-r)/q)`. Therefore

\[
\boxed{
v_p(U_n)=\sum_{a\ge1}\left(
 \left\lfloor{n+p^a-r_1(p^a)\over p^a}\right\rfloor+
 \left\lfloor{n+p^a-r_5(p^a)\over p^a}\right\rfloor
\right).}                                                 \tag{3.3}
\]

The sum is finite: its terms vanish once `p^a>6n-1`. Equivalently, because
`U_n` selects the integers coprime to 6,

\[
\boxed{
v_p(U_n)=\sum_{a\ge1}\left(
 \left\lfloor{6n\over p^a}\right\rfloor-
 \left\lfloor{3n\over p^a}\right\rfloor-
 \left\lfloor{2n\over p^a}\right\rfloor+
 \left\lfloor{n\over p^a}\right\rfloor
\right).}                                                 \tag{3.4}
\]

Equations (3.1)--(3.4) cover every prime and include every valuation layer;
there is no least-term uniqueness assumption.

## 4. Explicit 5-adic deviation and transient scale

For `n>=1`, put

\[
 A_5(n)=\lfloor\log_5(6n-1)\rfloor.
\]

At level `5^a`, each of the two residue-class counts in (3.3) differs from
`n/5^a` by less than one. Hence, writing `C_a(n)` for their sum,

\[
 |C_a(n)-2n/5^a|<2.                                      \tag{4.1}
\]

Since `sum_(a>=1)2n/5^a=n/2` and all actual counts vanish after `A_5(n)`,

\[
 v_5(U_n)-{n\over2}
 =\sum_{a=1}^{A_5(n)}(C_a(n)-2n/5^a)
   -{n\over2\,5^{A_5(n)}}.                              \tag{4.2}
\]

The tail is less than `5n/(2(6n-1))<=1/2`. Thus the following completely
explicit bounds hold for every `n>=1`:

\[
\boxed{
-2A_5(n)-\tfrac12<v_5(U_n)-\tfrac n2<2A_5(n).}           \tag{4.3}
\]

In particular `v_5(U_n)=n/2+O(log n)` with displayed constants. If

\[
 \tau_m=\min\{n\ge0:v_5(U_n)\ge m\}\quad(m\ge1),       \tag{4.4}
\]

then (3.3) computes `tau_m` exactly and (4.3) gives
`tau_m=2m+O(log m)`. This is only the cleared sequence's
5-adic zero transient modulo `10^m`; it is not yet the decimal-time transient
of `a_n`.

## 5. The actual reduced coefficient denominator

Write `a_n=P_n/q_n` in lowest terms, with `q_n>0`. From (2.4),

\[
v_p(q_n)=\max(2n v_p(6)+2v_p(n!)-v_p(U_n),0).             \tag{5.1}
\]

Equation (3.1) immediately gives

\[
 \alpha_n:=v_2(q_n)=2n+2v_2(n!),\qquad
 \beta_n:=v_3(q_n)=2n+2v_3(n!).                          \tag{5.2}
\]

For `p>=5`, subtracting `2v_p(n!)` from (3.4) gives a sum of terms

\[
 \lfloor6x\rfloor-\lfloor3x\rfloor-
 \lfloor2x\rfloor-\lfloor x\rfloor\ge0,                \tag{5.3}
\]

where `x=n/p^a` and the inequality is floor superadditivity applied to
`6x=3x+2x+x`.
Thus `v_p(U_n)>=2v_p(n!)` for every `p>=5`; all such denominator primes
cancel. Consequently

\[
\boxed{q_n=2^{\alpha_n}3^{\beta_n}.}                     \tag{5.4}
\]

Using the base-`p` digit sum `s_p(n)`, Legendre's formula makes this

\[
\boxed{\alpha_n=4n-2s_2(n),\qquad
       \beta_n=3n-s_3(n).}                               \tag{5.5}
\]

In particular `P_n` is a unit modulo 6. This complete reduction is the key
separation from an unreduced-modulus calculation.

## 6. Powers of 10, post-transient order, and occupancy

Fix `n>=1`. For decimal time `j>=0`, the denominator of `10^j a_n` in
lowest terms is

\[
\boxed{q_{n,j}=2^{\max(\alpha_n-j,0)}3^{\beta_n}.}        \tag{6.1}
\]

Indeed `P_n` is prime to 6 and `10^j` contributes exactly `2^j5^j`.
The decimal-time transient is therefore exactly `alpha_n`, not `tau_m` from
(4.4). At `j=alpha_n+s`,

\[
 10^j a_n\equiv
 {P_n5^{\alpha_n}10^s\over3^{\beta_n}}\pmod1.            \tag{6.2}
\]

The numerator in (6.2) is a unit modulo `3^{beta_n}`. By the elementary LTE
identity

\[
 v_3(10^r-1)=v_3(10-1)+v_3(r)=2+v_3(r)\quad(r\ge1),      \tag{6.3}
\]

the exact multiplicative order is

\[
\boxed{
d_n=\operatorname{ord}_{3^{\beta_n}}(10)=
\begin{cases}
1,&\beta_n\le2,\\
3^{\beta_n-2},&\beta_n\ge3.
\end{cases}}                                             \tag{6.4}
\]

Here `beta_1=2`; for every `n>=2`, `beta_n>=4`. Thus the post-transient
coefficient orbit has exactly `d_n` residues, each occupied once in every
complete period.

The full occupancy, including the transient, is also exact. For any prefix
length `N>=1`, let

\[
 C_n(N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
            10^ia_n\equiv10^ja_n\pmod1\}.                \tag{6.5}
\]

This is ordered and diagonal-inclusive. If `i<j`, reduction of the equality
shows

\[
 2^{\alpha_n}3^{\beta_n}\mid10^i(10^{j-i}-1).
\]

Because `10^{j-i}-1` is prime to 10, equality occurs exactly when

\[
 i\ge\alpha_n\quad\hbox{and}\quad d_n\mid(j-i).           \tag{6.6}
\]

Therefore every transient value is a singleton and is disjoint from the
tail. Put `L=max(N-alpha_n,0)` and

\[
 c_r(L)=\max\left(0,1+\left\lfloor{L-1-r\over d_n}\right\rfloor\right)
 \quad(0\le r<d_n).                                      \tag{6.7}
\]

The complete occupancy and collision formulas are

\[
\boxed{
C_n(N)=
\begin{cases}
N,&N\le\alpha_n,\\
\alpha_n+\displaystyle\sum_{r=0}^{d_n-1}c_r(L)^2,
  &N>\alpha_n.
\end{cases}}                                             \tag{6.8}
\]

No finite-table premise occurs in (6.1)--(6.8).
Equivalently, if `L=u d_n+v` with `0<=v<d_n`, the tail sum in
(6.8) is the constant-time expression

\[
 \sum_{r=0}^{d_n-1}c_r(L)^2
 =v(u+1)^2+(d_n-v)u^2.                                   \tag{6.9}
\]

## 7. Literal logarithmic-depth collision substitution

Fix integers `A>=1` and `n>=max(A,2)`. Take the post-transient block length

\[
 L=A n,
\]

and the full prefix length

\[
 N=\alpha_n+An.                                          \tag{7.1}
\]

Since `beta_n>=2n`, (6.4) gives `d_n>=9^(n-1)`. The elementary induction
`9^(n-1)>=n^2` for `n>=2`, followed by `n>=A`, gives

\[
 L=An\le n^2\le9^{n-1}\le d_n.                           \tag{7.2}
\]

Thus every one of the first `N` orbit values is distinct by (6.6), so the
literal ordered collision statistic is exactly

\[
 \boxed{C_n(N)=N.}                                       \tag{7.3}
\]

As `N>=An`, substitution gives the constant-explicit related-model bound

\[
 \boxed{A n C_n(N)=AnN\le N^2.}                          \tag{7.4}
\]

The depth is logarithmic in the actual reduced denominator. Indeed
`alpha_n<=4n`, so `N<=(A+4)n`, while (5.4) gives `q_n>=4^n`. Hence

\[
 \boxed{N\le {A+4\over\log4}\log q_n.}                  \tag{7.5}
\]

Equations (7.1)--(7.5), rather than a valuation asymptotic or finite table,
are the developed H1 model mechanism. They concern exact equality in one
rational orbit, not the canonical metric relation.

## 8. Prior and active fingerprints

All prior reports are vendored byte-exactly so the comparison is inspectable.
Their proof-sketch deductions are comparison memory only and are not premises
for Sections 2--7.

| Comparator and level | Normalized fingerprint | T126 boundary |
|---|---|---|
| T79, `proof sketch`, SHA `7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800` | A Machin-like rational approximation is reduced after a power-of-10 transient; exact order and equality occupancy survive, but the forced modulus makes an inspected square-root estimate longer than the transfer prefix. | T126 uses no approximation to pi and no exponential-sum theorem. Complete cancellation leaves the pure modulus `3^beta`; LTE then proves injectivity for the required logarithmic block. |
| T85, `proof sketch`, finite replay `experiment`, SHA `06fc459ab48d1d3cbe78a3038bdc76e20591ee86b7d243cba4a879a1e1fce2c7` | Tied least valuations require residue analysis; at its displayed scale the power-of-5 transient consumes the entire transferred prefix. | T126 uses the all-layer floor sum (3.3), not least-term uniqueness. Its decimal transient is exactly `alpha_n`, and the chosen prefix deliberately includes a nonempty tail of length `An`. |
| T112, sources `literature-checked`, deductions `proof sketch`, replay `experiment`, SHA `72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa` | Carry chains and finite transducers give random-input or signed-model spreading but miss the prescribed path and boundary observable. | T126 has a deterministic rational path and exact occupancy, with no carry or stationary-law averaging. It still has no pi path transfer. |
| T118, sources `literature-checked`, deductions `proof sketch`, replay `experiment`, SHA `2ed7a176bedb2f3a1627dffd4002f6b6141f078fe5c73798041b4fba90c7410e` | Private prime powers give exact order at logarithmic length, but available exponential-sum estimates require polynomial length or fail the exact numerator. | T126 needs only equality collisions, not phase cancellation. Its pure `3`-power order is enough to make the block injective; this does not solve T118's exponential-sum problem. |
| T121, sources `literature-checked`, deductions `proof sketch`, replay `experiment`, SHA `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2` | Walsh--Legendre averaging bounds aggregate word collisions at logarithmic depth; necklace and Stoneham cards are model overlaps. | T126's saving is pointwise multiplicative injectivity in one rational orbit, not aggregate character orthogonality or word energy. Both remain sibling collision models. |
| latest readable T123 report, workflow verdict `revise`, source claims `literature-checked`, deductions `proof sketch`, replay `experiment`, SHA `3eed848437e5ade5cfc0ac5c8f8fabf5968ff156262b74ea2d947413b74fecb2` | Named computable sibling points use de Bruijn prefixes, Levin discrepancy, a computable absolutely-normal selector with an unextracted discrepancy onset, and a Thue--Morse obstruction. Its T121-unavailable row is stale: current T121 discloses necklace overlap. | T126 uses a hypergeometric coefficient and exact reduced rational order, not normal-point construction or discrepancy. The shared scope is only a named related-model collision calculation. |
| active T125 | No report, source package, result, or mathematical fingerprint is readable in the binding snapshot; only active-task metadata was reported. | No content is inferred and no novelty claim is made against T125. |

The T123 comparison uses the latest globally readable report and records its
`revise` status rather than treating it as accepted evidence. T125 remains an
availability boundary.

## 9. Separately labeled pi-transfer premise

`PI-H1-COLL` (`conjecture`; unproved additional premise): for every integer
`A>=1` and all sufficiently large `n`, with `N=alpha_n+An`, there is an
explicit injection from the canonical ordered near-return set

\[
 \{(i,j)\in\{0,\ldots,N-1\}^2:
   \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}
\]

into the H1 equality-collision set counted by `C_n(N)` in (6.5), preserving
the diagonal and the ordered-pair convention.

This premise is intentionally strong and is not asserted. No inspected source
constructs the injection, relates `a_n` to pi, controls decimal carries, or
turns exact rational equality into the canonical circle-distance observable.
Conditionally it would transfer (7.4), but the report draws no such
conclusion. Stating `PI-H1-COLL` separately prevents the model calculation
from being mistaken for a fixed-point argument.

## 10. Replay and claim boundary

From a directory containing only the delivered files, run

```bash
python3 verify_t126.py
sha256sum -c SHA256SUMS
```

The Python verifier checks the pinned input hashes and finite instances of the
recurrence, both valuation formulas, bound (4.3), denominator reduction,
power-of-10 denominators, orders, occupancies, and substitutions. The separate
manifest command checks every report, input, script, and recorded output.
The source locator is inspectable in the vendored PDF; the script checks its
hash and PDF signature, not its page semantics. Every finite check and printed
table is an `experiment`. The proofs of the universal formulas are the
displayed elementary arguments, not extrapolations from that output.

What has been developed is exactly one related-model mechanism: complete
denominator reduction plus LTE yields a constant-explicit, logarithmic-depth,
ordered collision bound. It establishes no property of the fixed decimal
orbit, no canonical near-return estimate, and no claim about C1 or C2.

## 11. Scoped verdict

DEVELOP
