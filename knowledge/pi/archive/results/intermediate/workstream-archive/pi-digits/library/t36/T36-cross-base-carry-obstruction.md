# T36: Exact cross-base prefix carries and decimal-word avoidance

Status: `proof sketch` (elementary identities checked below, but no kernel
formalization). Terminal verdict: **FINITE-STATE OBSTRUCTION** in the precise,
limited sense of Section 8.

## 1. Provenance, exact target, and scope

- Canonical source: `pi-digits.txt`, a byte-exact vendored copy of the immutable
  human-authored root `knowledge/pi/statements/pi-digits.txt`.
- Canonical source SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
- Original external source URL: none. The root records Marcel's request of
  2026-07-21 as its provenance.
- Exact target: canonical V1, not sibling V2 or V3. V1 asks whether every
  finite word over `0,...,9`, including words beginning with zero, occurs
  contiguously in the decimal fractional digits of pi.

This note does **not** prove V1, V3, decimal normality of pi, or any
distribution property of pi's hexadecimal digits. Finite calculations in
`finite_prefix_diagnostics.py` are diagnostics for the displayed integer
identities only. By the canonical verification rule they have zero resolution
leverage for V1 or V3.

### Normalized quantifiers and ambiguities

1. In V1, the finite decimal word is chosen first and its occurrence position
   may depend on that word.
2. The empty word is vacuous. All avoidance claims below concern a fixed
   nonempty word `w` of length `k >= 1`.
3. Prefix lengths `n` (hexadecimal) and `m` (decimal) are independent positive
   integers unless a displayed formula says `m=n`.
4. All cylinders are half-open. This fixes endpoint ambiguity for terminating
   rationals. Pi is irrational, so its own expansion is not an endpoint case.
5. `tau_w` acts on all real numbers in `[0,1)`, not just pi. Following the one
   branch selected by pi would require exact hexadecimal information about pi.
6. The obstruction below concerns the exact integer carry representation of
   this particular operator. It does not prove that every conceivable quotient,
   symbolic recoding, or nonlocal algorithm must have infinitely many states.

## 2. Numbered definitions

**Definition 1 (word value and cylinder).** For a base `b >= 2` and a word
`u=(u_1,...,u_l)` with `0 <= u_i < b`, put

\[
[u]_b=\sum_{i=1}^{l}u_i b^{l-i},\qquad
C_b(u)=\left[\frac{[u]_b}{b^l},\frac{[u]_b+1}{b^l}\right).
\tag{D1}
\]

Leading zeros are retained through the separately recorded length `l`.
For `x in [0,1)`, `x in C_b(u)` exactly when
`floor(b^l x)=[u]_b`; hence `C_b(u)` fixes the first `l` floor-based base-`b`
digits of `x`.

**Definition 2 (cross-base compatibility and carry).** Let `u` be a
hexadecimal word of length `n`, let `v` be a decimal word of length `m`, and
write

\[
A=[u]_{16},\quad D=[v]_{10},\quad
\kappa_{n,m}(A,D)=10^mA-16^nD.                 \tag{D2}
\]

The pair `(u,v)` is *compatible* when `C_16(u) cap C_10(v)` is nonempty.
The integer `kappa` is its exact unnormalized carry (signed endpoint offset).

**Definition 3 (decimal avoidance).** `Avoid_w(v)` means that for every
`0 <= i <= m-k`, the length-`k` subword of `v` beginning at `i` differs from
`w`. When `m<k`, this condition is vacuous.

**Definition 4 (avoidance states).**

\[
S_w(n,m)=\{(u,v): |u|=n,\ |v|=m,\
 C_{16}(u)\cap C_{10}(v)\ne\varnothing,\ Avoid_w(v)\}.       \tag{D3}
\]

An exact implementation may store `(n,m,A,D)`. Equivalently for transition
purposes it may store the scales, the carry `kappa`, and enough prefix data to
recover validity and the last `k-1` decimal digits.

**Definition 5 (candidate operator `tau_w`).** If `r,s >= 1`, let `H` be an
`r`-digit hexadecimal block (`0 <= H < 16^r`) and `E` an `s`-digit decimal
block (`0 <= E < 10^s`, with leading zeros supplied by length `s`). For each
`S \subseteq S_w(n,m)`, define the typed set operator

\[
\tau_{w;n,m}^{r,s}:\mathcal P(S_w(n,m))\longrightarrow
\mathcal P(S_w(n+r,m+s)),
\]
\[
\tau_{w;n,m}^{r,s}(S)=\{(uH,vE): (u,v)\in S,\
 C_{16}(uH)\cap C_{10}(vE)\ne\varnothing,\ Avoid_w(vE)\}.    \tag{D4}
\]

Thus `tau_w` is a family indexed by the refinement sizes. It is deliberately
not called a finite automaton: finiteness or a uniform state quotient is the
question under test.

## 3. Exact rational interval identities

Let `A,D,n,m` be as in Definition 2. On the common denominator
`16^n 10^m`, the two cylinders are

\[
C_{16}(u)=\frac1{16^n10^m}[10^mA,10^m(A+1)),
\quad
C_{10}(v)=\frac1{16^n10^m}[16^nD,16^n(D+1)).                \tag{I1}
\]

Therefore their intersection is exactly

\[
\frac1{16^n10^m}
\left[
 \max(10^mA,16^nD),
 \min(10^m(A+1),16^n(D+1))
\right).                                                    \tag{I2}
\]

It is nonempty precisely when its signed integer overlap numerator

\[
L_{n,m}(A,D)=
\min(\kappa+10^m,16^n)-\max(\kappa,0)                      \tag{I3}
\]

is positive. (When the cylinders are disjoint, `L` is a signed overlap
numerator and can be nonpositive; only on compatible pairs is it an actual
positive numerator length.) Expanding the two strict endpoint inequalities gives the useful
equivalent carry test

\[
C_{16}(u)\cap C_{10}(v)\ne\varnothing
\quad\Longleftrightarrow\quad
-10^m<\kappa_{n,m}(A,D)<16^n.                              \tag{I4}
\]

These are identities of rational half-open intervals, not approximations.

## 4. Exact finite transition

Concatenation gives

\[
A'=16^rA+H,\qquad D'=10^sD+E.                              \tag{T1}
\]

Substitution in Definition 2 yields the exact transition

\[
\boxed{\ 
\kappa_{n+r,m+s}(A',D')
=10^s16^r\kappa_{n,m}(A,D)+10^{m+s}H-16^{n+r}E.
\ }                                                         \tag{T2}
\]

For the displayed synchronous case `r=s=1`, this is

\[
\kappa'=160\kappa+10^{m+1}h-16^{n+1}e.                    \tag{T3}
\]

After applying (T2), (I4) is an exact test for whether the child cylinders
overlap. Because Definition 5 restricts the parent to `S_w(n,m)`, avoidance
inside the old prefix is already known. Testing newly created occurrences then
needs only the old suffix of length at most `k-1` together with `E`; that
symbolic component is finite. The numeric carry and the two scales remain.

## 5. A displayed finite transition

Take `w=(2)` and the compatible level `(n,m)=(1,1)` state `A=D=0`, so
`kappa=0`. Its synchronous children retained by `tau_(2)^(1,1)` are:

```text
(h=0,e=0,carry=0) (h=1,e=0,carry=100) (h=2,e=0,carry=200) (h=2,e=1,carry=-56) (h=3,e=1,carry=44) (h=4,e=1,carry=144) (h=5,e=1,carry=244) (h=7,e=3,carry=-68) (h=8,e=3,carry=32) (h=9,e=3,carry=132) (h=A,e=3,carry=232) (h=A,e=4,carry=-24) (h=B,e=4,carry=76) (h=C,e=4,carry=176) (h=C,e=5,carry=-80) (h=D,e=5,carry=20) (h=E,e=5,carry=120) (h=F,e=5,carry=220) (h=F,e=6,carry=-36)
```

Each tuple is independently checked by (T3), (I4), and decimal avoidance.
The replay script also exhaustively checks the signed-numerator identity (I3)
and compatibility criterion (I4) at levels
`(1,1),(1,2),(2,1),(2,2)` and reports state/carry counts through `(3,3)`.
These finite checks detect transcription errors; they are not evidence about
pi or any universal asymptotic assertion.

## 6. Explicit growing exact-carry family

Fix `w=(2)`. At every synchronous level `n=m>=1`, take the top cylinders

\[
A_n=16^n-1,\qquad D_n=10^n-1.                              \tag{G1}
\]

The decimal word for `D_n` is `99...9`, so it avoids `2`. Both cylinders end
at `1`, and

\[
\kappa_n=10^n(16^n-1)-16^n(10^n-1)=16^n-10^n.             \tag{G2}
\]

Because `0<16^n-10^n<16^n`, criterion (I4) proves
`(A_n,D_n) in S_(2)(n,n)`. The arithmetically unavoidable common factor is

\[
g_n=\gcd(10^n,16^n)=2^n,                                  \tag{G3}
\]

so even the gcd-reduced carry is

\[
q_n=\kappa_n/g_n=8^n-5^n.                                 \tag{G4}
\]

This grows strictly: for `n>=1`,

\[
q_{n+1}-q_n=7\cdot8^n-4\cdot5^n>0,
\]

and `q_n >= 3*8^(n-1)`, since
`8^n-5^n >= 8^n-5*8^(n-1)=3*8^(n-1)`. Hence the exact
gcd-reduced carry coordinate is unbounded along states that survive this
avoidance operator.

This proves a growing exact-coordinate obstruction for the state representation
specified in Definitions 2, 4, and 5: neither raw `kappa` nor its obvious
gcd reduction lies in a level-independent finite set. Formula (T2) also
retains the unbounded scales `10^m` and `16^n`.

It does **not** prove a Myhill-Nerode lower bound or exclude a subtler finite
quotient that forgets exact carries while somehow preserving all future
acceptance decisions. Establishing or refuting such a quotient is an open gap,
not silently included in the terminal verdict.

## 7. A precise conditional bridge to T20

This section records a clean but currently unproved assumption; it is not
derived from the carry calculation or from BBP digit extraction.

For `x in [0,1)`, let `{y}=y-floor(y)`. For every hexadecimal word `u` and
decimal word `v`, define the **joint cross-base mixing hypothesis** `JMix(x)`:

\[
\lim_{N\to\infty}\frac1N\sum_{j=0}^{N-1}
 1_{C_{16}(u)}(\{16^j x\})
 1_{C_{10}(v)}(\{10^j x\})
=16^{-|u|}10^{-|v|}.                                      \tag{M1}
\]

The empty word is allowed and its cylinder is `[0,1)`. Taking `u` empty in
(M1) gives, for every decimal cylinder `C_10(v)`, limiting visit frequency
`10^(-|v|)>0`. Thus `{10^j x}` enters every decimal cylinder and is dense in
`[0,1]` (cylinders form arbitrarily fine meshes; proximity to `1` follows from
the cylinders with all digits `9`). For every `j`,

\[
\{10^j\{\pi\}\}=\{10^j\pi\},                              \tag{M2}
\]

because `10^j floor(pi)` is an integer. The machine-checked T20 theorem
`v1_iff_pi_baseTenOrbitDense` then gives the conditional implication

\[
JMix(\{\pi\})\quad\Longrightarrow\quad\text{canonical V1}. \tag{M3}
\]

`JMix({pi})` is **unproved** and is much stronger than the desired occurrence
statement: its empty-hex marginal already asserts base-10 normal frequencies.
Accordingly, (M3) is an exact interface, not progress toward discharging V1.
It also says nothing specifically about sibling V3 beyond consequences V1
would have through separately established results.

T20 source pin: `BaseTenOrbitDensity.lean`, SHA-256
`202d6db7dfc2f19db81c3cb96b856d36969652e54099c43e0d51b6ab62913126`;
the supplied knowledge index records its named theorems at `lean-gate`
verification.

### Why T12's counterexamples do not satisfy `JMix`

The T12 literature audit records Schmidt's map `T_(10,2)`: for almost every
binary input it produces a base-2-normal real whose decimal expansion uses
only digits `0` and `1`. For such an `x`, the decimal cylinder
`C_10((2))=[2/10,3/10)` is never visited by `{10^j x}`. In (M1), choose the
empty hexadecimal word and `v=(2)`. The left side is identically zero while
the right side is `1/10`. Therefore these counterexamples fail `JMix`
explicitly. Base-2 normality alone supplies no missing joint-mixing premise.

Source pin: Wolfgang M. Schmidt, *On Normal Numbers*, Pacific J. Math. 10
(1960), 661-672, Theorem 2, DOI
<https://doi.org/10.2140/pjm.1960.10.661>; retained publisher PDF SHA-256
`28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67`.
The T12 audit is literature-checked for its dated bounded source set; this note
does not upgrade any broader absence-of-literature claim.

## 8. Terminal verdict

**FINITE-STATE OBSTRUCTION (for the exact carry-state proposal).** The exact candidate `tau_w` has a finite
decimal-suffix component, but its exact gcd-reduced carry component has the
explicit surviving values `8^n-5^n` and is therefore not uniformly bounded.
Consequently it cannot be implemented by a fixed finite state table whose
states retain the exact gcd-reduced carry together with the decimal suffix.

Scope limitation: no theorem here excludes every possible finite quotient or
proves anything about pi's actual branch. The only displayed route to T20 is
conditional on the explicit, unproved `JMix({pi})`, which already contains a
base-10 normality marginal. The finite calculations are diagnostics only.

## 9. Reproduction

From a directory containing only these delivered files, run:

```sh
./reproduce.sh
```

The script verifies retained file hashes, verifies the canonical source hash,
recomputes all displayed finite transitions with exact integers, and compares
the output byte-for-byte with `expected-output.txt`.

## 10. Literature-search log

| Date | Bounded source/query | Result used |
|---|---|---|
| 2026-08-01 | Retained T6 BBP/Bailey-Crandall source map | BBP-scale digit extraction and conditional base-2 normality do not themselves state a decimal transfer theorem. |
| 2026-08-01 | Retained T12 Schmidt audit and pinned primary PDF | Supplies explicit arbitrary-real base-transfer counterexamples used in Section 7. |
| 2026-08-01 | Retained T35 novelty audit, base-expansion and disjunctivity entries | T20's cylinder/orbit equivalence is machine-checked; no claim of novelty for the elementary cylinder identities is made. |

This was a bounded reuse search of the supplied knowledge library, not an
exhaustive literature review.
