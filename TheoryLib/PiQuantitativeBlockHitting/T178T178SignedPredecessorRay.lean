import TheoryLib.PiQuantitativeBlockHitting.T176T176SignedBlockBellmanTransport

/-!
# T178: an infinite signed predecessor ray

The strict prefix Bellman step from T176 can be iterated coherently.  Starting
from any decimal scale `q₀ ≥ 1000`, target `A₀ < q₀`, and nonempty prefix, this
module chooses one predecessor digit at every level.  The resulting targets
form a single ten-adic ray and their signed Bellman surplus strictly increases.

This is a structural theorem.  Positivity of the root surplus remains an
explicit hypothesis; in particular, no finite experiment concerning `π` is
promoted to the verified track here.
-/

noncomputable section

namespace Theory.PiDigits.SignedPredecessorRay

open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.SignedBlockBellmanTransport

/-- The prefix score after subtracting the T176 coarse potential. -/
def signedPrefixSurplus (q A L : ℕ) : ℝ :=
  q * (primitiveBoundaryFourierSum q A L).re -
    L * signedBlockPotential q

/-- A chosen improving predecessor digit.  The fallback branch makes the
definition total; it is never used on the ray constructed below. -/
noncomputable def improvingDigit (q A L : ℕ) : ℕ :=
  if h : 1000 ≤ q ∧ 0 < L then
    Classical.choose (exists_leftExtension_prefix_bellman_gt q A L h.1 h.2)
  else 0

theorem improvingDigit_lt_ten
    (q A L : ℕ) (hq : 1000 ≤ q) (hL : 0 < L) :
    improvingDigit q A L < 10 := by
  rw [improvingDigit, dif_pos ⟨hq, hL⟩]
  exact (Classical.choose_spec
    (exists_leftExtension_prefix_bellman_gt q A L hq hL)).1

theorem signedPrefixSurplus_improvingDigit_gt
    (q A L : ℕ) (hq : 1000 ≤ q) (hL : 0 < L) :
    signedPrefixSurplus (10 * q) (A + improvingDigit q A L * q) L >
      signedPrefixSurplus q A L := by
  rw [improvingDigit, dif_pos ⟨hq, hL⟩]
  exact (Classical.choose_spec
    (exists_leftExtension_prefix_bellman_gt q A L hq hL)).2

/-- The scale at level `r` of a decimal predecessor ray. -/
def rayModulus (q₀ r : ℕ) : ℕ := q₀ * 10 ^ r

/-- The targets obtained by repeatedly choosing the T176 improving digit. -/
noncomputable def rayTarget (q₀ A₀ L : ℕ) : ℕ → ℕ
  | 0 => A₀
  | r + 1 =>
      rayTarget q₀ A₀ L r +
        improvingDigit (rayModulus q₀ r) (rayTarget q₀ A₀ L r) L *
          rayModulus q₀ r

/-- The predecessor digit selected at level `r`. -/
noncomputable def rayDigit (q₀ A₀ L r : ℕ) : ℕ :=
  improvingDigit (rayModulus q₀ r) (rayTarget q₀ A₀ L r) L

theorem rayModulus_succ (q₀ r : ℕ) :
    rayModulus q₀ (r + 1) = 10 * rayModulus q₀ r := by
  unfold rayModulus
  rw [pow_succ]
  ring

theorem rayModulus_ge (q₀ r : ℕ) (hq₀ : 1000 ≤ q₀) :
    1000 ≤ rayModulus q₀ r := by
  unfold rayModulus
  exact hq₀.trans (Nat.le_mul_of_pos_right q₀ (by positivity))

theorem rayDigit_lt_ten
    (q₀ A₀ L r : ℕ) (hq₀ : 1000 ≤ q₀) (hL : 0 < L) :
    rayDigit q₀ A₀ L r < 10 := by
  exact improvingDigit_lt_ten _ _ _ (rayModulus_ge q₀ r hq₀) hL

theorem rayTarget_zero (q₀ A₀ L : ℕ) :
    rayTarget q₀ A₀ L 0 = A₀ := rfl

theorem rayTarget_succ (q₀ A₀ L r : ℕ) :
    rayTarget q₀ A₀ L (r + 1) =
      rayTarget q₀ A₀ L r +
        rayDigit q₀ A₀ L r * rayModulus q₀ r := rfl

theorem rayTarget_lt_modulus
    (q₀ A₀ L : ℕ) (hA₀ : A₀ < q₀) (hq₀ : 1000 ≤ q₀)
    (hL : 0 < L) :
    ∀ r, rayTarget q₀ A₀ L r < rayModulus q₀ r := by
  intro r
  induction r with
  | zero => simpa [rayModulus] using hA₀
  | succ r ihr =>
      rw [rayTarget_succ, rayModulus_succ]
      have hd := rayDigit_lt_ten q₀ A₀ L r hq₀ hL
      have hdle : rayDigit q₀ A₀ L r ≤ 9 := by omega
      have hmul := Nat.mul_le_mul_right (rayModulus q₀ r) hdle
      omega

theorem signedPrefixSurplus_ray_strictMono
    (q₀ A₀ L : ℕ) (hq₀ : 1000 ≤ q₀) (hL : 0 < L) (r : ℕ) :
    signedPrefixSurplus (rayModulus q₀ r) (rayTarget q₀ A₀ L r) L <
      signedPrefixSurplus (rayModulus q₀ (r + 1))
        (rayTarget q₀ A₀ L (r + 1)) L := by
  rw [rayModulus_succ, rayTarget_succ]
  exact signedPrefixSurplus_improvingDigit_gt
    (rayModulus q₀ r) (rayTarget q₀ A₀ L r) L
    (rayModulus_ge q₀ r hq₀) hL

theorem signedPrefixSurplus_root_le_ray
    (q₀ A₀ L : ℕ) (hq₀ : 1000 ≤ q₀) (hL : 0 < L) :
    ∀ r,
      signedPrefixSurplus q₀ A₀ L ≤
        signedPrefixSurplus (rayModulus q₀ r) (rayTarget q₀ A₀ L r) L := by
  intro r
  induction r with
  | zero => simp [rayModulus, rayTarget]
  | succ r ihr =>
      exact ihr.trans (signedPrefixSurplus_ray_strictMono q₀ A₀ L hq₀ hL r).le

/-- A positive root surplus gives an explicit positive score lower bound at
every level of the coherent ray. -/
theorem primitiveBoundaryFourierSum_ray_lower_bound
    (q₀ A₀ L : ℕ) (hq₀ : 1000 ≤ q₀) (hL : 0 < L)
    (hroot : 0 < signedPrefixSurplus q₀ A₀ L) (r : ℕ) :
    (L : ℝ) * 7 / (3 * (rayModulus q₀ r : ℝ) ^ 2) <
      (primitiveBoundaryFourierSum
        (rayModulus q₀ r) (rayTarget q₀ A₀ L r) L).re := by
  have hsurplus : 0 < signedPrefixSurplus
      (rayModulus q₀ r) (rayTarget q₀ A₀ L r) L :=
    hroot.trans_le (signedPrefixSurplus_root_le_ray q₀ A₀ L hq₀ hL r)
  have hq : (0 : ℝ) < rayModulus q₀ r := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1000)
      (rayModulus_ge q₀ r hq₀))
  unfold signedPrefixSurplus signedBlockPotential at hsurplus
  field_simp
  field_simp at hsurplus
  nlinarith

/-- Bundled conditional infinite-ray theorem.  The root score is deliberately
left as a hypothesis: T178 does not certify any experimental `π` seed. -/
theorem exists_infinite_signed_predecessor_ray
    (q₀ A₀ L : ℕ) (hq₀ : 1000 ≤ q₀) (hA₀ : A₀ < q₀) (hL : 0 < L) :
    ∃ A d : ℕ → ℕ,
      A 0 = A₀ ∧
      (∀ r, d r < 10) ∧
      (∀ r, A (r + 1) = A r + d r * rayModulus q₀ r) ∧
      (∀ r, A r < rayModulus q₀ r) ∧
      (∀ r,
        signedPrefixSurplus (rayModulus q₀ r) (A r) L <
          signedPrefixSurplus (rayModulus q₀ (r + 1)) (A (r + 1)) L) := by
  refine ⟨rayTarget q₀ A₀ L, rayDigit q₀ A₀ L, rfl, ?_, ?_, ?_, ?_⟩
  · exact fun r => rayDigit_lt_ten q₀ A₀ L r hq₀ hL
  · exact fun r => rayTarget_succ q₀ A₀ L r
  · exact rayTarget_lt_modulus q₀ A₀ L hA₀ hq₀ hL
  · exact fun r => signedPrefixSurplus_ray_strictMono q₀ A₀ L hq₀ hL r

end Theory.PiDigits.SignedPredecessorRay

#print axioms Theory.PiDigits.SignedPredecessorRay.exists_infinite_signed_predecessor_ray
#print axioms Theory.PiDigits.SignedPredecessorRay.primitiveBoundaryFourierSum_ray_lower_bound
