import TheoryLib.PiLongLagBlockCollisionDecay.T1T1LongLagBlockCollisionDecay

/-!
# T19: deterministic sparse periodic islands

This generic digit-stream sibling formalizes only the deterministic collision
mechanism.  Its ordered-pair and weak nonoverlap conventions agree with the
canonical definitions imported above.
-/

noncomputable section

open Finset Filter

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T19

/-- A zero-based base-ten digit stream. -/
abbrev DecimalStream := ℕ → Fin 10

/-- The length-`m` block beginning at zero-based start `i`. -/
def streamBlock (d : DecimalStream) (i m : ℕ) : Fin m → Fin 10 :=
  fun r => d (i + r)

/-- The generic analogue of the canonical ordered long-lag collision set. -/
def orderedCollisionPairs (d : DecimalStream) (m N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun ij =>
    m ≤ Nat.dist ij.1 ij.2 ∧ streamBlock d ij.1 m = streamBlock d ij.2 m

/-- The cardinality of the generic ordered long-lag collision set. -/
def streamCollisionCount (d : DecimalStream) (m N : ℕ) : ℕ :=
  (orderedCollisionPairs d m N).card

/-- A finite family of starts for one common block, including the exact
sample-size and pairwise nonoverlap hypotheses used by ordered counting. -/
structure CommonBlockStartsCertificate (d : DecimalStream) (m N q : ℕ)
    (starts : Finset ℕ) (word : Fin m → Fin 10) : Prop where
  card_starts : starts.card = q
  starts_lt : ∀ i ∈ starts, i < N
  nonoverlap : ∀ i ∈ starts, ∀ j ∈ starts, i ≠ j → m ≤ Nat.dist i j
  carries_word : ∀ i ∈ starts, streamBlock d i m = word

/-- `q` common, pairwise nonoverlapping starts contribute all `q*(q-1)`
ordered off-diagonal pairs. -/
theorem commonBlockStarts_orderedCollision_lower_bound
    {d : DecimalStream} {m N q : ℕ} {starts : Finset ℕ}
    {word : Fin m → Fin 10}
    (hcard : starts.card = q)
    (hstarts : ∀ i ∈ starts, i < N)
    (hnonoverlap : ∀ i ∈ starts, ∀ j ∈ starts,
      i ≠ j → m ≤ Nat.dist i j)
    (hword : ∀ i ∈ starts, streamBlock d i m = word) :
    q * (q - 1) ≤ streamCollisionCount d m N := by
  classical
  have hsubset : starts.offDiag ⊆ orderedCollisionPairs d m N := by
    intro ij hij
    rw [Finset.mem_offDiag] at hij
    rw [orderedCollisionPairs, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (hstarts ij.1 hij.1),
          Finset.mem_range.mpr (hstarts ij.2 hij.2.1)⟩,
      hnonoverlap ij.1 hij.1 ij.2 hij.2.1 hij.2.2,
      (hword ij.1 hij.1).trans (hword ij.2 hij.2.1).symm⟩
  calc
    q * (q - 1) = starts.offDiag.card := by
      rw [Finset.offDiag_card, hcard]
      rw [Nat.mul_sub_left_distrib]
      simp
    _ ≤ (orderedCollisionPairs d m N).card := Finset.card_le_card hsubset
    _ = streamCollisionCount d m N := rfl

/-- The starts of `q` consecutive periods in an island. -/
def periodicStarts (A m q : ℕ) : Finset ℕ :=
  (Finset.range q).image fun t => A + t * m

/-- A reusable certificate for `q` complete copies of one length-`m` block,
starting at `A` and lying within the prefix of length `N`. -/
structure PeriodicIslandCertificate
    (d : DecimalStream) (A m q N : ℕ) : Prop where
  period_pos : 0 < m
  island_fits : A + q * m ≤ N
  periodic : ∀ t < q, streamBlock d (A + t * m) m = streamBlock d A m

theorem periodicStarts_card {A m q : ℕ} (hm : 0 < m) :
    (periodicStarts A m q).card = q := by
  unfold periodicStarts
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range q
  · intro t u htu
    apply Nat.mul_right_cancel hm
    exact Nat.add_left_cancel htu

theorem periodicIsland_commonBlockStarts
    {d : DecimalStream} {A m q N : ℕ}
    (cert : PeriodicIslandCertificate d A m q N) :
    CommonBlockStartsCertificate d m N q (periodicStarts A m q)
      (streamBlock d A m) := by
  classical
  refine
    { card_starts := periodicStarts_card cert.period_pos
      starts_lt := ?_
      nonoverlap := ?_
      carries_word := ?_ }
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨t, ht, rfl⟩
    have htq : t < q := Finset.mem_range.mp ht
    have hmul : t * m < q * m := Nat.mul_lt_mul_of_pos_right htq cert.period_pos
    exact lt_of_lt_of_le (Nat.add_lt_add_left hmul A) cert.island_fits
  · intro i hi j hj hij
    rcases Finset.mem_image.mp hi with ⟨t, ht, rfl⟩
    rcases Finset.mem_image.mp hj with ⟨u, hu, rfl⟩
    have htu : t ≠ u := by
      intro h
      exact hij (congrArg (fun v => A + v * m) h)
    have hdist : 1 ≤ Nat.dist t u := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hzero
      exact htu (Nat.eq_of_dist_eq_zero hzero)
    calc
      m = 1 * m := by simp
      _ ≤ Nat.dist t u * m := Nat.mul_le_mul_right m hdist
      _ = Nat.dist (A + t * m) (A + u * m) := by
        rw [Nat.dist_add_add_left, Nat.dist_mul_right]
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨t, ht, rfl⟩
    exact cert.periodic t (Finset.mem_range.mp ht)

/-- Every certified periodic island contributes the expected ordered count. -/
theorem periodicIsland_orderedCollision_lower_bound
    {d : DecimalStream} {A m q N : ℕ}
    (cert : PeriodicIslandCertificate d A m q N) :
    q * (q - 1) ≤ streamCollisionCount d m N := by
  have hcommon := periodicIsland_commonBlockStarts cert
  exact commonBlockStarts_orderedCollision_lower_bound hcommon.card_starts
    hcommon.starts_lt hcommon.nonoverlap hcommon.carries_word

/-- Positive scale parameter used by the explicit infinite schedule. -/
def scheduleScale (k : ℕ) : ℕ := k + 1

/-- Start of the scheduled sparse island. -/
def scheduleStart (k : ℕ) : ℕ := 10 ^ (5 * scheduleScale k)

/-- Common block length in the scheduled island. -/
def scheduleBlockLength (k : ℕ) : ℕ := 20 * scheduleScale k

/-- Number of complete periods in the scheduled island. -/
def schedulePeriodCount (k : ℕ) : ℕ := 10 ^ (3 * scheduleScale k)

/-- Prefix length containing the entire scheduled island. -/
def scheduleSampleSize (k : ℕ) : ℕ :=
  scheduleStart k + schedulePeriodCount k * scheduleBlockLength k

/-- Every scale of the explicit schedule is certified in `d`. -/
def SatisfiesSparsePeriodicSchedule (d : DecimalStream) : Prop :=
  ∀ k, PeriodicIslandCertificate d (scheduleStart k)
    (scheduleBlockLength k) (schedulePeriodCount k) (scheduleSampleSize k)

/-- The additive-`N` comparison scale from the collision predicate. -/
def collisionComparison (s : ℝ) (m N : ℕ) : ℝ :=
  (N : ℝ) + (N : ℝ) ^ 2 * (10 : ℝ) ^ (-s * (m : ℝ))

/-- The generic collision predicate at one fixed exponent. -/
def StreamCollisionDecayAt (d : DecimalStream) (s : ℝ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
    (streamCollisionCount d m N : ℝ) ≤ C * collisionComparison s m N

theorem schedule_parameters
    (k : ℕ) :
    0 < scheduleBlockLength k ∧
      scheduleStart k + schedulePeriodCount k * scheduleBlockLength k =
        scheduleSampleSize k := by
  constructor
  · simp [scheduleBlockLength, scheduleScale]
  · rfl

theorem twenty_mul_le_hundred_pow (t : ℕ) : 20 * t ≤ 100 ^ t := by
  calc
    20 * t ≤ 100 * t := Nat.mul_le_mul_right t (by norm_num)
    _ ≤ 100 ^ t := Nat.mul_le_pow (a := 100) (by norm_num) t

theorem schedule_periodic_length_le_start (k : ℕ) :
    schedulePeriodCount k * scheduleBlockLength k ≤ scheduleStart k := by
  let t := scheduleScale k
  have ht : 20 * t ≤ 10 ^ (2 * t) := by
    calc
      20 * t ≤ 100 ^ t := twenty_mul_le_hundred_pow t
      _ = 10 ^ (2 * t) := by
        rw [pow_mul]
        norm_num
  calc
    schedulePeriodCount k * scheduleBlockLength k =
        10 ^ (3 * t) * (20 * t) := by
      rfl
    _ ≤ 10 ^ (3 * t) * 10 ^ (2 * t) :=
      Nat.mul_le_mul_left _ ht
    _ = 10 ^ (5 * t) := by
      have hexp : 3 * t + 2 * t = 5 * t := by omega
      rw [← pow_add]
      rw [hexp]
    _ = scheduleStart k := rfl

theorem scheduleSampleSize_le_two_start (k : ℕ) :
    scheduleSampleSize k ≤ 2 * scheduleStart k := by
  unfold scheduleSampleSize
  have h := schedule_periodic_length_le_start k
  omega

/-- Successive scheduled islands are disjoint: the current island is wholly
contained before the next island start. -/
theorem scheduleSampleSize_le_next_start (k : ℕ) :
    scheduleSampleSize k ≤ scheduleStart (k + 1) := by
  calc
    scheduleSampleSize k ≤ 2 * scheduleStart k :=
      scheduleSampleSize_le_two_start k
    _ ≤ 10 ^ 5 * scheduleStart k :=
      Nat.mul_le_mul_right (scheduleStart k) (by norm_num)
    _ = scheduleStart (k + 1) := by
      unfold scheduleStart scheduleScale
      rw [← pow_add]
      congr 1
      omega

theorem scheduleStart_pos (k : ℕ) : 0 < scheduleStart k := by
  unfold scheduleStart
  positivity

theorem constantStream_satisfiesSparsePeriodicSchedule (a : Fin 10) :
    SatisfiesSparsePeriodicSchedule (fun _ => a) := by
  intro k
  refine
    { period_pos := (schedule_parameters k).1
      island_fits := le_of_eq (schedule_parameters k).2
      periodic := ?_ }
  intro t ht
  funext r
  rfl

theorem scheduleStart_cast_sq (k : ℕ) :
    (scheduleStart k : ℝ) ^ 2 =
      ((10 ^ (10 * scheduleScale k) : ℕ) : ℝ) := by
  exact_mod_cast show scheduleStart k ^ 2 =
      10 ^ (10 * scheduleScale k) by
    unfold scheduleStart
    rw [← pow_mul]
    congr 1
    omega

theorem schedule_half_decay_eq_inv_sq (k : ℕ) :
    (10 : ℝ) ^ (-(1 / 2 : ℝ) * (scheduleBlockLength k : ℝ)) =
      ((scheduleStart k : ℝ) ^ 2)⁻¹ := by
  rw [scheduleStart_cast_sq]
  have hexp : -(1 / 2 : ℝ) * (scheduleBlockLength k : ℝ) =
      -((10 * scheduleScale k : ℕ) : ℝ) := by
    simp only [scheduleBlockLength, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hexp]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast]
  exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)
    ((10 * scheduleScale k : ℕ) : ℝ)

/-- At the selected exponent `s=1/2`, the explicit schedule's additive-`N`
comparison is at most six times its island-start scale. -/
theorem schedule_additiveN_comparison (k : ℕ) :
    collisionComparison (1 / 2 : ℝ) (scheduleBlockLength k)
        (scheduleSampleSize k) ≤
      6 * (scheduleStart k : ℝ) := by
  have hApos : (0 : ℝ) < scheduleStart k := by
    exact_mod_cast scheduleStart_pos k
  have hAone : (1 : ℝ) ≤ scheduleStart k := by
    exact_mod_cast (scheduleStart_pos k)
  have hN : (scheduleSampleSize k : ℝ) ≤
      2 * (scheduleStart k : ℝ) := by
    exact_mod_cast scheduleSampleSize_le_two_start k
  have hNnonneg : (0 : ℝ) ≤ scheduleSampleSize k := by positivity
  have hAnonneg : (0 : ℝ) ≤ scheduleStart k := hApos.le
  have hsq : (scheduleSampleSize k : ℝ) ^ 2 ≤
      (2 * (scheduleStart k : ℝ)) ^ 2 := by
    nlinarith
  have hexponential :
      (scheduleSampleSize k : ℝ) ^ 2 *
          ((scheduleStart k : ℝ) ^ 2)⁻¹ ≤ 4 := by
    calc
      (scheduleSampleSize k : ℝ) ^ 2 *
            ((scheduleStart k : ℝ) ^ 2)⁻¹ ≤
          (2 * (scheduleStart k : ℝ)) ^ 2 *
            ((scheduleStart k : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (sq_nonneg _))
      _ = 4 := by
        field_simp [hApos.ne']
        norm_num
  unfold collisionComparison
  rw [schedule_half_decay_eq_inv_sq]
  nlinarith

theorem schedulePeriodCount_sq_eq_scale_mul_start (k : ℕ) :
    schedulePeriodCount k * schedulePeriodCount k =
      10 ^ scheduleScale k * scheduleStart k := by
  unfold schedulePeriodCount scheduleStart
  rw [← pow_add, ← pow_add]
  congr 1
  omega

theorem two_le_schedulePeriodCount (k : ℕ) :
    2 ≤ schedulePeriodCount k := by
  unfold schedulePeriodCount
  have hexp : 1 ≤ 3 * scheduleScale k := by
    unfold scheduleScale
    omega
  calc
    2 ≤ 10 ^ 1 := by norm_num
    _ ≤ 10 ^ (3 * scheduleScale k) :=
      Nat.pow_le_pow_right (by norm_num) hexp

/-- The explicit schedule has an unbounded ordered-collision ratio at
`s=1/2`, stated with the quantifiers needed to refute any proposed constant. -/
theorem sparsePeriodicSchedule_unbounded_collision_ratio
    {d : DecimalStream} (hd : SatisfiesSparsePeriodicSchedule d) :
    ∀ C : ℝ, ∃ k : ℕ,
      C * collisionComparison (1 / 2 : ℝ) (scheduleBlockLength k)
          (scheduleSampleSize k) <
        (streamCollisionCount d (scheduleBlockLength k)
          (scheduleSampleSize k) : ℝ) := by
  intro C
  let C0 : ℝ := max C 0
  obtain ⟨n, hn⟩ := exists_nat_gt (12 * C0)
  refine ⟨n, ?_⟩
  let D := collisionComparison (1 / 2 : ℝ) (scheduleBlockLength n)
    (scheduleSampleSize n)
  let A : ℝ := scheduleStart n
  let q : ℕ := schedulePeriodCount n
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hCC0 : C ≤ C0 := le_max_left _ _
  have hDnonneg : 0 ≤ D := by
    unfold D collisionComparison
    positivity
  have hD : D ≤ 6 * A := by
    exact schedule_additiveN_comparison n
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast scheduleStart_pos n
  have hnPower : n < 10 ^ scheduleScale n := by
    calc
      n < 10 ^ n := Nat.lt_pow_self (by norm_num)
      _ ≤ 10 ^ scheduleScale n := by
        apply Nat.pow_le_pow_right
        · norm_num
        · simp [scheduleScale]
  have hpower : 12 * C0 < ((10 ^ scheduleScale n : ℕ) : ℝ) :=
    hn.trans (by exact_mod_cast hnPower)
  have hscaled := mul_lt_mul_of_pos_right hpower hApos
  have hbeforeSquare : C * D < (q : ℝ) ^ 2 / 2 := by
    have hqSquare : (q : ℝ) ^ 2 =
        ((10 ^ scheduleScale n : ℕ) : ℝ) * A := by
      dsimp [q, A]
      rw [pow_two]
      exact_mod_cast (schedulePeriodCount_sq_eq_scale_mul_start n)
    calc
      C * D ≤ C0 * D := mul_le_mul_of_nonneg_right hCC0 hDnonneg
      _ ≤ C0 * (6 * A) := mul_le_mul_of_nonneg_left hD hC0
      _ < ((10 ^ scheduleScale n : ℕ) : ℝ) * A / 2 := by
        nlinarith
      _ = (q : ℝ) ^ 2 / 2 := by rw [hqSquare]
  have hcountNat := periodicIsland_orderedCollision_lower_bound (hd n)
  have hqTwo : 2 ≤ q := two_le_schedulePeriodCount n
  have hqSq : q * q ≤ 2 * (q * (q - 1)) := by
    have hlinear : q ≤ 2 * (q - 1) := by omega
    calc
      q * q ≤ q * (2 * (q - 1)) := Nat.mul_le_mul_left q hlinear
      _ = 2 * (q * (q - 1)) := by ring
  have hqCount : q * q ≤
      2 * streamCollisionCount d (scheduleBlockLength n)
        (scheduleSampleSize n) :=
    hqSq.trans (Nat.mul_le_mul_left 2 hcountNat)
  have hhalfCount : (q : ℝ) ^ 2 / 2 ≤
      (streamCollisionCount d (scheduleBlockLength n)
        (scheduleSampleSize n) : ℝ) := by
    have hcast : (q : ℝ) ^ 2 ≤
        2 * (streamCollisionCount d (scheduleBlockLength n)
          (scheduleSampleSize n) : ℝ) := by
      rw [pow_two]
      exact_mod_cast hqCount
    linarith
  exact hbeforeSquare.trans_le hhalfCount

/-- Every stream carrying the explicit schedule fails the collision predicate
at the selected exponent `s=1/2`. -/
theorem sparsePeriodicSchedule_fails_collisionDecayAt_half
    {d : DecimalStream} (hd : SatisfiesSparsePeriodicSchedule d) :
    ¬ StreamCollisionDecayAt d (1 / 2 : ℝ) := by
  rintro ⟨C, _hC, hbound⟩
  obtain ⟨k, hbad⟩ := sparsePeriodicSchedule_unbounded_collision_ratio hd C
  have hm : 1 ≤ scheduleBlockLength k := (schedule_parameters k).1
  have hN : 1 ≤ scheduleSampleSize k := by
    have hstart : 1 ≤ scheduleStart k := scheduleStart_pos k
    unfold scheduleSampleSize
    omega
  have hgood := hbound (scheduleBlockLength k) (scheduleSampleSize k) hm hN
  exact (not_lt_of_ge hgood) hbad

end Theory.PiDigits.LongLagBlockCollisionDecay.T19

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.commonBlockStarts_orderedCollision_lower_bound
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.periodicStarts_card
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.periodicIsland_commonBlockStarts
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.periodicIsland_orderedCollision_lower_bound
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.schedule_parameters
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.scheduleSampleSize_le_next_start
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.constantStream_satisfiesSparsePeriodicSchedule
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.schedule_additiveN_comparison
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.sparsePeriodicSchedule_unbounded_collision_ratio
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T19.sparsePeriodicSchedule_fails_collisionDecayAt_half
