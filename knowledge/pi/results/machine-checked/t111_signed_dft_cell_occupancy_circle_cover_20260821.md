# T111 signed-DFT cell occupancy and circle cover

Status: `machine-checked`

Canonical source:
`TheoryLib/PiQuantitativeBlockHitting/T111T111SelectedNumeratorFourierCover.lean`

Canonical SHA-256:
`3fd73b753df5bce6177159a4760db6bd8df04519602664ab363f47fae27d352f`

## Result

For any finite real sample and nonzero mesh size `q`, T111 proves:

1. the full cell-centered DFT equals `q` times the exact cell multiplicity;
2. if the real part of the signed nonzero-frequency sum is strictly greater
   than `-M`, then the selected cell is occupied;
3. two reals in the same cyclic mesh cell have `UnitAddCircle` distance at
   most `q⁻¹`;
4. hitting every cyclic cell therefore gives a `q⁻¹` circle cover.

The signed criterion is one-sided. It does not replace the required input by
Parseval energy, absolute values, or symmetric moments. The geometric proof
uses the quotient-circle metric and handles the zero/one endpoint without
equating it to ordinary real distance.

## Verification and provenance

- Three independently generated DFT candidates and three independently
  generated circle-cover candidates passed isolated Lean/axiom gates.
- The canonical DFT proof was distilled from Oxzen candidate SHA-256
  `102836dc4847724df2eb24e47112198f034cfba5b949101d8056abc949d4324b`.
- The canonical geometric proof was distilled from Oxzen candidate SHA-256
  `9330fdef24ca43514f374bc63562b9bca86c91d06845074697bd025ffaff51c0`.
  Its first attempt contained `sorry` and was rejected; only the clean second
  attempt was reviewed and used.
- Independent semantic review checked character orthogonality, the signed
  implication, `q = 1`, `M = 0`, floor-cell lifting, and quotient endpoints.
- `pwsh workflows/verification/check.ps1` passed on 2026-08-21: the full
  current Lean build, forbidden-marker/exploit scan, and exact axiom allowlist.
- All four registered public theorems depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.

## Boundary

This is generic finite infrastructure. It supplies no estimate for the sampled
BBP orbit, no signed trough bound, no density theorem, no prescribed decimal
word, and no V1 conclusion. It is not a novelty or literature claim. The next
workstream must apply the certificate to structure that retains the full exact
BBP numerator, denominator, and synchronized coefficient system; same-fiber
or marginal-residue replacements are insufficient.
