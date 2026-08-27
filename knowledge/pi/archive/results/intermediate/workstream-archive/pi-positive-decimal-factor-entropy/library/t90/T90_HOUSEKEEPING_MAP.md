# T90 housekeeping map

Status: exact mapping of scheduler-reported gaps to accepted artifacts. This
document makes no claim that the canonical positive-entropy question is
resolved.

The canonical statement is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`, SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
It requires one fixed real `eta > 0` and one fixed integer `N >= 1` such that
every `n >= N` satisfies the stated lower bound. None of the interfaces below
discharges that open assertion.

## Exact gap map

| Report | Disposition | Exact accepted locator |
|---|---|---|
| T1 lacked a reusable prefix-suffix injection and factor-count submultiplicativity interface. | Covered; imported, not duplicated. Both declarations are public and generic in the finite alphabet and stream. | `knowledge_library/t1/CanonicalEntropy.lean`, SHA-256 `8f424db10d98a42ab0e547b2abdef0db9c5b45443c05a4e01033502a2934dbdf`, `DecimalFactorEntropy.splitFactor_injective` at lines 53-66 and `DecimalFactorEntropy.canonicalFactorComplexity_submultiplicative` at lines 68-77. |
| T3 lacked directly reusable finite Parseval. | Covered; imported, not duplicated. The proof expands the transform and uses `AddChar.sum_apply_eq_ite`, then passes from the complex conjugate-product identity to squared norms. | `knowledge_library/t3/FiniteFourierObstruction.lean`, SHA-256 `5bb975c9107c5a1862e269b85a9797c195a6f96747b8f35c41e80e5de808c798`, `DecimalFactorEntropy.FiniteFourierObstruction.finiteFourier_conj_mul_sum` at lines 92-113 and public theorem `finiteFourier_parseval` at lines 120-128. |
| T3's distinct-factor-cell coefficient was not identified with T10's time-indexed ordinary orbit sum. | Still deliberately open; no transfer theorem is claimed. | T3 states the nonidentification at lines 18-20 and defines `factorCellFourier` from the uniform distinct-cell distribution at lines 376-380. T10's `ordinaryOrbitSum` instead sums over time indices. `T90Housekeeping.lean` imports both relevant dependency chains but adds no equality between them. |
| Original adjacent record directories used by T5 were absent. | Covered by exact content-addressed references rather than copied records. | `knowledge_library/t5/SOURCE_MANIFEST.md`, SHA-256 `a1d9bbac1e5043476c3f2053ec4cdf2c65179acfee63ee03c1f3c397547bdb05`, lines 36-64; `knowledge_library/t5/DELTA_AUDIT.md`, SHA-256 `93089b4f44db9e295d1f8f560adf5b5b2922e624abfd084b92f6cfb8a0543129`. |
| T8's `circleDistance` upper bound lacked an attained integer representative. | Covered; imported, not duplicated. The witness is `round y`; the proof uses `round_le` and `abs_sub_round`. | `knowledge_library/t8/T8DyadicShellFejer.lean`, SHA-256 `dd73354bf5d978e97722f8c13eda61305c279a5bee8d7c107db04168c1f21ce1`, public theorem `DecimalFactorComplexity.DyadicShellFejer.exists_int_circleDistance_eq_abs_le_half` at lines 105-117. |
| The adjacent T11/T24 irrationality-measure audit was not recopied into this library. | Covered by T5's accepted content-addressed manifest and applicability audit. This is a provenance mapping, not a new mathematical proof. | T5 `SOURCE_MANIFEST.md` line 49 pins T11's audit, manifest, and receipt as `8661237d2363358c4f2328fb974c693b5f2abaff40470a9eb8340cece34a4b4f`, `caf0f52164d53e5e965ae0523fda342b6f34f52d6ab63d16f0361048ea2cd6e7`, and `dafd9dadcac2279f02d3d2d2930405e59955f2379da13f84f2a30cc6abb2af58`; line 53 pins T24's audit, corpus, and receipt as `fedbf2ae2f990ddd57442d240989f878be9db1868a0fde9b85534572cdfab0bd`, `ba716f7deb6c82c33366cfb4f569c904d59d70283860a4ae7ab5e6be1c924b53`, and `95a85aae4b6fc49b573292621f2fdb09052865594cdcc5f9f7bc154172cb0fd5`. T5 `DELTA_AUDIT.md` lines 154-157 records the `literature-checked` conclusion: the ZZ20 irrationality measure gives individual separation, not aggregate pair sparsity or Fourier cancellation. |
| T15 lacked a checked character-preserving discretization from a T10 coefficient to a finite-group set with controlled multiplicities and errors; an overstrong energy comparison was removed. | The stronger set/common-model transfer remains absent and no energy comparison is restored. Later T18 covers only a per-sample multiplicity measure: exact coefficient normalization and controlled floor-quantization error. It does not produce a common positive-density set, scale-uniform additive energy, or identify T3's distinct-factor distribution. | `knowledge_library/t15/T15_INVERSE_STRUCTURE_AUDIT.md`, SHA-256 `d68e9b853a4628a01252834178c2b1dc8a9dc2c113135491543579569796cb01`, lines 231-240 and 281-305. The partial later interfaces are T18 `finiteFourier_orbitCellMeasure_eq` at lines 95-111 and `simultaneous_quantizedOrbitSum_error` at lines 267-293. |
| T18 lacked a reusable two-point Lipschitz theorem for imaginary exponentials. | Covered; imported, not duplicated. The proof factors the difference by the unit-norm exponential at the second point and invokes mathlib's one-point estimate. | `knowledge_library/t18/T18FiniteCircleQuantization.lean`, SHA-256 `9c999d3a15e7f179680d8123deeae9b066cbbf3c39d235acb0b20d24f085ec70`, public theorem `DecimalFactorComplexity.FiniteCircleQuantization.norm_exp_I_mul_sub_exp_I_mul_le` at lines 153-168. |

## Public import surface

`T90Housekeeping.lean` imports the accepted T1, T3, T8, and T18 modules. It
intentionally introduces no aliases or replacement declarations: importing it
makes the existing public, general signatures available transitively while
avoiding duplicate declarations in the aggregate `TheoryLib` environment.

## Scope

This delivery is housekeeping. It proves neither C1 nor its negation, does not
upgrade T15's bounded literature audit into a theorem, does not identify the
T3 and T10 coefficient objects, and does not infer additive energy from T18's
per-witness quantization.
