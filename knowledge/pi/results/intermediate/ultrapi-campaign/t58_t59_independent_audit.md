# Independent adversarial audit: T58 Hutton bracket and T59 cylinder certificate

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: the immutable local question has no external source URL; none is
invented here.

Audited files and their bytes at the audit point:

| File | SHA-256 |
|---|---|
| [`T58T58HuttonRationalShadow.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T58T58HuttonRationalShadow.lean) | `bfae5a8a52419c1ab864ab919c58d083262dac59668db5aae6f574ba51581da6` |
| [`T59T59HuttonCylinderCertificate.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T59T59HuttonCylinderCertificate.lean) | `cc55b40b78ef75ad014dafd158beba888f49a9694db20165d949c1667e615d80` |
| [`TheoryLib.lean`](../../TheoryLib.lean) | `5c3f2bd5744bb6c787d670557291e1697ba501b436f29a5107a411659c76e189` |
| [`AxiomAudit.lean`](../../audit/AxiomAudit.lean) | `372434161be515d3d727e300e3f2741533668fc5669c9352f819af66a466770c` |
| [`ultrapi.md`](../../ultrapi.md) | `bf1edc370be4bde8b62745fa8b6a80a63ecb8e7ef7163c7ea9a8f1c27c074a6f` |

## Verdict

**PASS, with three documentation-only corrections listed below.**  I found
no mathematical, indexing, boundary, registration, axiom-surface, or
forbidden-construct defect in the 18 audited declarations.  T58 and T59
retain status `machine-checked` at exactly their stated scope.

They do **not** establish an existential decimal-cylinder containment, a hit
for an arbitrary prescribed word, density, recurrence, normality, or V1.
Consequently V1 remains a `conjecture`; these modules are not a `candidate
resolution` or a `verified resolution`.

## 1. T58 definition, identity, parity, and width audit

T58 defines

\[
 H_K=8T_3(2(K+1))+4T_7(2(K+1)),
 \qquad
 U_K=8T_3(2(K+1)+1)+4T_7(2(K+1)+1),
\]

where `arctanPartialRat q terms` sums indices
(0\le n<\text{terms}).  Thus the lower endpoint contains (2K+2)
terms, an even number, and the upper endpoint contains the adjacent (2K+3)
terms, an odd number.  At (K=0) these are respectively the two-term and
three-term Taylor sums.  There is no off-by-one or reversed-parity defect.

The imported mathlib theorem is literally

\[
 2\arctan(1/3)+\arctan(1/7)=\pi/4.
\]

Multiplication by four gives T58's normalization

\[
 \pi=8\arctan(1/3)+4\arctan(1/7).
\]

Both coefficients are positive.  The imported alternating-series lemmas say
an even-length sum is at most its arctangent and an odd-length sum is at least
its arctangent.  The directions in
`huttonLower_le_pi` and `pi_le_huttonUpper` are therefore correct.

The upper endpoint adds the Taylor term with index
(n=2(K+1)), which is even.  Its sign is positive, its odd denominator index
is

\[
 2n+1=4K+5,
\]

and its base power has the same exponent.  Hence

\[
 U_K-H_K=
 {8\over(4K+5)3^{4K+5}}+{4\over(4K+5)7^{4K+5}}>0.
\]

This agrees with `huttonUpperRat_sub_lowerRat`,
`huttonUpper_sub_lower_eq_width`, `huttonWidth_eq_explicit`, and
`huttonWidth_pos`.  The formal enclosure is non-strict,
(H_K\le\pi\le U_K); strict positivity separately proves (H_K<U_K).
T58 does not claim that either inequality involving pi is strict.

An independent exact Lean replay at (K=0) checked

\[
 H_0={87112\over27783},\qquad
 U_0={64162748\over20420505},\qquad
 U_0-H_0={135428\over20420505}
 ={8\over5\cdot3^5}+{4\over5\cdot7^5}.
\]

## 2. T59 scaled-cylinder algebra

For the generic theorem put

\[
 X=10^N x,\qquad q=10^m.
\]

Its premises are exactly

\[
 a<q,\qquad z+{a\over q}\le X<z+{a+1\over q}.             \tag{1}
\]

The range premise gives (a+1\le q).  Therefore (1) first gives
(z\le X<z+1), hence

\[
 \lfloor X\rfloor=z.
\]

Multiplication of (1) by the positive integer (q) gives

\[
 qz+a\le qX<qz+a+1,
\]

and hence

\[
 \lfloor qX\rfloor=qz+a.
\]

Finally (10^{N+m}x=qX), so direct substitution into

\[
 \operatorname{decimalBlockCode}(x,N,m)
 =\lfloor10^{N+m}x\rfloor-10^m\lfloor10^Nx\rfloor
\]

gives the value (a).  This is exactly the proof implemented in T59; the
cast directions and `pow_add` use are correct.  The bracket theorem composes
the monotone scaling inequalities in the correct directions, and the Hutton
specialization supplies the two enclosure hypotheses from T58.

### Boundary convention

The left boundary in (1) is inclusive and the right boundary is strict.
That is the correct half-open decimal cylinder

\[
 [z+a/10^m,\ z+(a+1)/10^m).
\]

If (X) equals the left endpoint, its code is (a).  If it equals the right
endpoint, its code is (a+1) (or the next whole-number cell at the last
label), and T59 deliberately does not apply because its upper premise is
strict.  The closed Hutton bracket may touch the cylinder's included left
edge; its upper endpoint must stay strictly below the excluded right edge.

Independent exact Lean examples checked all of the following:

- the included left endpoint (x=2.3) has one-digit code 3;
- the excluded right endpoint (x=0.2) has code 2, not code 1;
- (x=-1.7), using (z=-2), has code 3, confirming floor rather than
  truncation-toward-zero behavior;
- at (m=0), `a < 10^m` forces the unique label (a=0), and the code is 0;
- at (m=3), (a=7) represents the padded block `007`;
- for (x=3.1415), (N=2,m=2) gives code 15, confirming that (N) is the
  zero-based start after two fractional digits; and
- the T59 Hutton specialization is non-vacuous: (K=0,N=0,m=1,a=1,z=3)
  certifies `(piCylinderCode 1 0).val = 1` because the whole (K=0) bracket
  lies in ([3.1,3.2)).

The scratch audit file contained twelve `example` declarations and compiled
cleanly with `lake env lean`; its SHA-256 was
`a1f9abe262ba06d873c71ecbfeb6c31999acac6d209a96d882bec38c9f8e6d7b`.
It was kept outside the repository because it is audit replay, not a new
verified-track theorem.

### Symbolic bridge and leading zeroes

T59's last theorem rewrites through T37's already `machine-checked` identity

\[
 \operatorname{decimalBlockCode}(\pi,N,m)
 = (\operatorname{piCylinderCode}(m,N)).\mathrm{val}.
\]

T37 in turn identifies this value with the contiguous `blockAt piDigit m N`
word, where digit zero is the first fractional digit.  The length (m) is
retained in the type `Fin (10^m)`, so a numerical label such as 7 at (m=3)
means `007`, not the one-digit word `7`.  At (m=0), `Fin 1` supplies the
unique empty-word code.  T59's wording about zero-based indexing, leading
zeroes, and length zero is therefore accurate.

## 3. Registrations, imports, and forbidden constructs

The registered surface is exactly 18 propositions:

- 14 T58 declarations, from `huttonLower_eq` through
  `pi_mem_hutton_bracket`; and
- 4 T59 declarations, from
  `decimalBlockCode_eq_of_mem_scaled_cylinder` through
  `piCylinderCode_val_eq_of_hutton_bracket`.

An exact-name count found every one of these 18 `#print axioms` registrations
**once and only once** in `audit/AxiomAudit.lean`.  Both T58 and T59 are also
imported exactly once in `TheoryLib.lean` and exactly once in
`audit/AxiomAudit.lean`.  The similarly numbered T58/T59 modules in other
namespaces do not collide with these declarations.

A focused scan found none of the prohibited declarations or shortcuts:
`sorry`, `admit`, a new `axiom`, `native_decide`, `unsafe`, `opaque`, or
`constant`.  The files use an ordinary `noncomputable section`, which is not
an unsafe or compiler-trusting shortcut.  `git diff --check` passed for the
two modules, both import surfaces, and `ultrapi.md`.

## 4. Build and axiom replay

The following commands all exited successfully:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T58T58HuttonRationalShadow.lean
lake env lean TheoryLib/PiQuantitativeBlockHitting/T59T59HuttonCylinderCertificate.lean
lake env lean audit/AxiomAudit.lean
lake env lean /tmp/t58_t59_audit.lean
```

Each of the 18 focused `#print axioms` results reported exactly

```text
[propext, Classical.choice, Quot.sound]
```

and no additional axiom.  The complete direct audit compilation also exited
zero.  These are precisely the repository's allowed logical dependencies.
The repository's already recorded T59-integrated full gate is consistent with
this replay; this independent audit did not need to modify the gate.

## 5. `ultrapi.md` wording audit

The substantive T58/T59 descriptions are accurate:

- the status table states the exact bracket and exact width, then explicitly
  denies a decimal-orbit hit;
- equation (11bo) matches T58 term for term;
- equation (11bq) matches T59's inclusive lower and strict upper hypotheses;
- the text correctly records zero-based (N), leading-zero words, and
  (m=0); and
- it explicitly says that existence of (K,N,z) for each word is still
  unproved.

I found three documentation-only items to correct after this audit:

1. `ultrapi.md` equation (11br) currently has the malformed TeX exponent
   `3^{,4K+3-...}`.  The stray comma should be removed.  This equation belongs
   to the later periodic-orbit `proof sketch`, not to T58 or T59, so it does
   not affect their Lean statements.
2. The resume snapshot still says “T58/T59 independent review still
   pending.”  This report is the completed automated independent review; the
   snapshot should be updated without implying human expert review.
3. T59's source comment says its scaled endpoints fit “strictly inside” the
   cylinder.  The theorem correctly permits equality at the included left
   endpoint.  “Contained in the half-open cylinder” would be exact wording.
   Likewise, the nearby `ultrapi.md` sentence about “independent GMP
   arithmetic through (N=5000)” should identify its actual Machin checker
   rather than read as evidence for T58/T59; I did not rely on it here.

These are wording/provenance issues only.  The theorem statements and proofs
need no change based on this audit.

## 6. Exact scope boundary

T58 provides, for each **supplied** (K), a rational interval known to
contain pi.  T59 provides, for **supplied** (K,N,m,a,z), an implication from
two interval-containment inequalities to one exact block value.  Neither file
contains a theorem with the missing quantifiers

\[
 \forall m\ \forall a<10^m\ \exists K,N,z
\]

that make those containment inequalities true.  Full rational-period
coverage would not by itself supply a transferable occurrence position.
Therefore no existential containment, every-word conclusion, or V1 follows
from T58/T59, separately or together.
