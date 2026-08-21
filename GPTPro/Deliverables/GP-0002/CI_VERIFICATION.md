# GP-0002 CI verification

- Commit under test: `15e3a0e37cd6b81a916a9eca90024a37d2b7b120`
- Run ID: `32525961854`
- Run attempt: `1`
- Runner: `ubuntu-latest`
- Lean setup outcome: `success`
- Isolated T110 build exit: `0`
- Deterministic promotion exit: `2`
- Promotion changed canonical files: `false`
- Strict repository gate exit: `125`

## Isolated T110 build output (last 400 lines)

```text
info: TheoryLib/PiDecimalFactorComplexity/T10PiWeightedFourierReduction.lean:1238:0: 'DecimalFactorComplexity.WeightedFourierReduction.majorantPairSum_eq_doubleFrequencySum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiDecimalFactorComplexity/T10PiWeightedFourierReduction.lean:1239:0: 'DecimalFactorComplexity.WeightedFourierReduction.card_doubleFrequencyFiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiDecimalFactorComplexity/T10PiWeightedFourierReduction.lean:1240:0: 'DecimalFactorComplexity.WeightedFourierReduction.normalizedIntegralCoefficientFiber_eq_majorantCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
warning: TheoryLib/PiDecimalFactorComplexity/T10PiWeightedFourierReduction.lean:1240:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
info: TheoryLib/PiDecimalFactorComplexity/T10PiWeightedFourierReduction.lean:1241:0: 'DecimalFactorComplexity.WeightedFourierReduction.Q_pi_explicit_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiDecimalFactorComplexity/T10PiWeightedFourierReduction.lean:1242:0: 'DecimalFactorComplexity.WeightedFourierReduction.HFE_pi_implies_lacunaryNearReturnC2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
⚠ [8490/8496] Built TheoryLib.PiQuantitativeBlockHitting.T5PiQuantitativeResonanceObstruction (5.0s)
warning: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:1:1: * '-/':
Copyright too short!


Note: This linter can be disabled with `set_option linter.style.header false`
info: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:242:0: 'Theory.PiDigits.QuantitativeResonanceObstruction.C1_of_eventual_fullContainment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:243:0: 'Theory.PiDigits.QuantitativeResonanceObstruction.exists_piOrbit_resonance_of_missingBefore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
warning: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:243:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
info: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:244:0: 'Theory.PiDigits.QuantitativeResonanceObstruction.normalized_piOrbit_resonance_of_missing_fullContainment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
warning: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:244:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
info: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:245:0: 'Theory.PiDigits.QuantitativeResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_resonance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
warning: TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean:245:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
⚠ [8491/8496] Built TheoryLib.PiQuantitativeBlockHitting.T6PiNaturalScaleResonanceObstruction (14s)
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:1:1: * '-/':
Copyright too short!


Note: This linter can be disabled with `set_option linter.style.header false`
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:239:4: `simp [edgeSign, edgeFrequency]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:240:4: `simp_rw [hphase]` uses `⊢`!
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:239:4: `simp [edgeSign, edgeFrequency]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:241:4: `rw [← hneg]` uses `⊢`!
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:239:4: `simp [edgeSign, edgeFrequency]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:242:4: `simp_rw [div_eq_mul_inv]` uses `⊢`!
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:239:4: `simp [edgeSign, edgeFrequency]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:243:4: `simp_rw [← mul_assoc]` uses `⊢`!
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:239:4: `simp [edgeSign, edgeFrequency]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:244:4: `rw [← Finset.mul_sum, ← Finset.mul_sum]` uses `⊢`!
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:361:2: `simp [jacksonCoefficient]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:361:2: Try this:
  [apply] simp only [sum_ite_eq', Finset.mem_univ, ↓reduceIte, one_div]
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:362:2: `calc
  (∑ i : Bool × Fin n, -(edgeSign i * edgeSign i) / (2 * (n : ℝ) ^ 2)) =
      (∑ i : Bool × Fin n, edgeSign i ^ 2) * ((n : ℝ)⁻¹ ^ 2 * (-1 / 2)) :=
    by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
  _ = -(n : ℝ)⁻¹ := by
    rw [hsum]
    field_simp` uses `⊢`!
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:469:0: `finiteFourierPresentation_resonance` does not use the following hypothesis in its type:
  • [DecidableEq ι] (#3)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
warning: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:719:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:742:0: 'Theory.PiDigits.PiNaturalScaleResonanceObstruction.finite_empty_decimalInterval_resonance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:743:0: 'Theory.PiDigits.PiNaturalScaleResonanceObstruction.piOrbit_naturalScale_resonance_of_missingBefore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:744:0: 'Theory.PiDigits.PiNaturalScaleResonanceObstruction.normalized_piOrbit_naturalScale_resonance_of_missing_fullContainment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean:745:0: 'Theory.PiDigits.PiNaturalScaleResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_naturalScale_resonance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
⚠ [8492/8496] Built TheoryLib.PiQuantitativeBlockHitting.T8PiNoV1NaturalScaleResonance (5.2s)
warning: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:1:1: * '-/':
Copyright too short!


Note: This linter can be disabled with `set_option linter.style.header false`
warning: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:21:0: `exists_absent_extension` does not use the following hypothesis in its type:
  • [DecidableEq α] (#3)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
warning: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:21:0: `exists_absent_extension` does not use the following hypothesis in its type:
  • [Fintype α] (#2)

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
warning: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:42:0: `exists_absent_extension_of_missing_list` does not use the following hypothesis in its type:
  • [DecidableEq α] (#3)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
warning: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:42:0: `exists_absent_extension_of_missing_list` does not use the following hypothesis in its type:
  • [Fintype α] (#2)

Consider replacing this hypothesis with the corresponding instance of `Finite` and using `Fintype.ofFinite` in the proof, or removing it entirely.

Note: This linter can be disabled with `set_option linter.unusedFintypeInType false`
warning: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:87:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
warning: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:112:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
info: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:126:0: 'Theory.PiDigits.PiNoV1NaturalScaleResonance.exists_absent_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:127:0: 'Theory.PiDigits.PiNoV1NaturalScaleResonance.exists_absent_extension_of_missing_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean:128:0: 'Theory.PiDigits.PiNoV1NaturalScaleResonance.not_C1_implies_unbounded_naturalScale_resonance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
⚠ [8493/8496] Built TheoryLib.PiQuantitativeBlockHitting.T14T14BoundaryRobustFejerDichotomy (18s)
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1:1: * '-/':
Copyright too short!


Note: This linter can be disabled with `set_option linter.style.header false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:352:27: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:422:59: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:399:5: unused variable `hq`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:406:27: 'push_cast' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:514:29: This simp argument is unused:
  Set.mem_Icc

Hint: Omit it from the simp argument list.
  simp only [Set.mem_uIcc, S̵e̵t̵.̵m̵e̵m̵_̵I̵c̵c̵,̵ ̵not_or]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:573:31: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:627:65: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:698:68: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:842:32: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:842:32: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:813:54: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:835:25: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:837:58: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:947:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1080:25: unused variable `hq`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1080:38: unused variable `ha`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1211:8: 'push_cast' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1231:5: unused variable `hq`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1231:18: unused variable `hzero`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1429:38: unused variable `hk`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1572:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.fejerKernel_eq_aggregated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1573:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.integral_fejerKernel_tail_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1574:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.cylinderIndicator_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1575:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.fejerApproximation_eq_aggregated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1576:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.norm_fejerApproximation_sub_indicator_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1577:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.fejerEstimator_error_and_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1578:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.finite_emptyCylinder_dichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1579:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.cylinder_hit_of_small_boundary_and_aggregated_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1580:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.all_cylinders_hit_of_small_boundary_and_aggregated_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1581:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.finite_emptyCylinder_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1582:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.pi_fullContainment_at_exact_deadline_of_smallness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1583:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.not_C1_implies_unbounded_boundary_or_aggregated_resonance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean:1584:0: 'Theory.PiDigits.BoundaryRobustFejerDichotomy.not_C1_implies_unbounded_explicit_boundary_or_aggregated_resonance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
⚠ [8494/8496] Built TheoryLib.PiQuantitativeBlockHitting.T16T16DecimalBoundaryWordObstruction (14s)
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1:1: * '-/':
Copyright too short!


Note: This linter can be disabled with `set_option linter.style.header false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:47:39: unused variable `hb`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:75:8: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [List.cons_append, Theory.PiDigits.T20.wordValue, List.length_append, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵ih]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:221:52: This simp argument is unused:
  Nat.zero_mod

Hint: Omit it from the simp argument list.
  simp only [Nat.add_mod, Nat.mod_self, zero_add, N̵a̵t̵.̵z̵e̵r̵o̵_̵m̵o̵d̵,̵ ̵Nat.mod_mod]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:312:5: unused variable `hk`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:312:18: unused variable `hr`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:403:41: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:406:41: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:403:23: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:403:37: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:406:23: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:406:37: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:568:19: unused variable `hk`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:568:32: unused variable `hr`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1000:17: unused variable `hk`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1099:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.boundaryLabels_complete_carry_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1100:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.boundaryWords_complete_carry_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1101:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.piFractionalOrbit_avoids_grid_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1102:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.circular_grid_boundary_iff_adjacent_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1103:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.pi_twoBoundary_iff_four_fine_cylinders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1104:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.pi_twoBoundaryCount_eq_four_fine_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1105:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.missing_coarseCylinder_removes_two_interiors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1106:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.natCeil_eighth_eq_rounded_division' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1107:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.boundary_branch_forces_adjacent_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1108:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.decimal_width_t14_hypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1109:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.pi_fullContainment_at_decimal_width_exact_deadline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean:1110:0: 'Theory.PiDigits.DecimalBoundaryWordObstruction.not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
⚠ [8495/8496] Built TheoryLib.PiQuantitativeBlockHitting.T17T17PowerTenDiophantineReduction (6.3s)
warning: TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean:1:1: * '-/':
Copyright too short!


Note: This linter can be disabled with `set_option linter.style.header false`
info: TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean:420:0: 'Theory.PiDigits.PowerTenDiophantineReduction.zero_run_gives_powerTen_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean:421:0: 'Theory.PiDigits.PowerTenDiophantineReduction.nine_run_gives_powerTen_approximation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean:422:0: 'Theory.PiDigits.PowerTenDiophantineReduction.powerTenDiophantine_excludes_adjacent_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean:423:0: 'Theory.PiDigits.PowerTenDiophantineReduction.adjacentWordCounts_eq_zero_at_exact_deadline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean:424:0: 'Theory.PiDigits.PowerTenDiophantineReduction.powerTenDiophantine_excludes_boundary_branch_at_exact_deadline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean:425:0: 'Theory.PiDigits.PowerTenDiophantineReduction.not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
⚠ [8496/8496] Built TheoryLib.PiQuantitativeBlockHitting.T110T110PostT17CancellationCriterion (4.6s)
warning: TheoryLib/PiQuantitativeBlockHitting/T110T110PostT17CancellationCriterion.lean:1:1: * '-/':
Copyright too short!


Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (8496 jobs).
```

## Deterministic promotion output

```text
python3: can't open file '/home/runner/work/PI/PI/GPTPro/Deliverables/GP-0002/promote_t110.py': [Errno 2] No such file or directory
```

## Strict repository gate output (last 400 lines)

```text
not run: deterministic promotion failed
```

RESULT: FAIL
