# T118 normalized excess-residue cell guidance

Work only on the exact pointwise representation endpoint after canonical
T117. Do not attempt to prove that any cell is hit.

For each `N`, use the actual reduced rationals

- `Q = 10^N * bbpPartial (7*N)`, with signed numerator `A=Q.num` and
  positive denominator `D=Q.den`;
- `F = sampledBBPForcingRat N`, with signed numerator `C=F.num` and
  positive denominator `E=F.den`.

Define
`H=gcd D E`, `d=D/H`, `e=E/H`,
`X=10*A*e+C*d`, `k=Int.gcd X (H*d)`, and
`W=H*d*e/k`. The normalized signed numerator is `X/(k:ℤ)`. Its Euclidean
residue is

`R = (X/(k:ℤ)) % (W:ℤ)`.

Preserve those signed and Euclidean conventions literally. Do not replace
`X/(k:ℤ)` by a natural absolute value, a nonnegative numerator, `% q`, or a
least residue at another modulus. Prove `0<k` and `0<W` for the actual Rat
specialization before using remainder inequalities or division lemmas.

Use T114 for the actual gcd-normalized successor pair and T117 for
`U=H*X`, `g=H*k`, and `V/g=W`. Cancellation of the positive common factor
`H` must be justified for both integer Euclidean division and natural
division. The final interval is half-open and endpoint-exact:

`a*W ≤ q*R ∧ q*R < (a+1)*W`.

The hypotheses `0<q` and `a<q`, together with `0≤R<W`, are essential when
lifting equality from `ZMod q` back to the unique integer cell representative.
Do not weaken `<` to `≤`, introduce real approximations, or reason by floating
point.

The task ends at the pointwise equivalence. It asserts neither existence nor
arbitrarily-late recurrence of a solution. Do not define or prove a density,
occupancy, cancellation, normality, digit-occurrence, or V1 statement. Finite
examples are unnecessary and are not evidence.

Only `Contribution.lean` and a concise `REPORT.md` are deliverables. The Lean
file must import exactly the controller-allowed canonical T117 module, declare
all four frozen theorems with their exact signatures, contain no command
output, and compile without forbidden shortcuts.
