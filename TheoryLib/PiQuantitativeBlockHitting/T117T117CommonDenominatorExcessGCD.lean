import TheoryLib.PiQuantitativeBlockHitting.T116T116SampledBBPGCDPrimeSupport

/-!
# T117: complete excess-gcd decomposition for the reduced cross-sum pair

For signed numerators `A C : ℤ` and natural denominators `D E : ℕ`, this
module removes their automatic common-denominator factor exactly. It proves
no size inequality, cancellation, occupancy, density, normality, or V1 claim.
-/

namespace Theory.PiDigits.T117CommonDenominatorExcessGCD

/-- After division by their positive gcd, two natural numbers are coprime. -/
theorem gcdQuotients_coprime :
    ∀ (D E : ℕ), 0 < Nat.gcd D E →
      Nat.Coprime (D / Nat.gcd D E) (E / Nat.gcd D E) := by
  intro D E hpos
  have hD : Nat.gcd D E ∣ D := Nat.gcd_dvd_left D E
  have hE : Nat.gcd D E ∣ E := Nat.gcd_dvd_right D E
  have key : Nat.gcd D E * (D / Nat.gcd D E).gcd (E / Nat.gcd D E) =
      Nat.gcd D E := by
    have h := Nat.gcd_mul_left (Nat.gcd D E)
      (D / Nat.gcd D E) (E / Nat.gcd D E)
    rw [Nat.mul_comm (Nat.gcd D E) (D / Nat.gcd D E),
      Nat.div_mul_cancel hD,
      Nat.mul_comm (Nat.gcd D E) (E / Nat.gcd D E),
      Nat.div_mul_cancel hE] at h
    exact h.symm
  have h1 : (D / Nat.gcd D E).gcd (E / Nat.gcd D E) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [mul_one]
    exact key
  exact h1

private theorem excessNumerator_coprime_aux (A C : ℤ) (D E H d e : ℕ)
    (hH : H = Nat.gcd D E) (hd : d = D / H) (he : e = E / H)
    (hCE : Nat.Coprime C.natAbs E) (hpos : 0 < H) :
    Nat.Coprime (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs e := by
  have hgc : Nat.gcd D E = H := hH.symm
  have hHD : H ∣ D := by rw [← hgc]; exact Nat.gcd_dvd_left D E
  have hHE : H ∣ E := by rw [← hgc]; exact Nat.gcd_dvd_right D E
  have hDd : D = d * H := by rw [hd]; exact (Nat.div_mul_cancel hHD).symm
  have hEe : E = e * H := by rw [he]; exact (Nat.div_mul_cancel hHE).symm
  have hEdiv : e ∣ E := ⟨H, hEe⟩
  have hcde : Nat.Coprime d e := by
    have h := gcdQuotients_coprime D E (by rw [hgc]; exact hpos)
    rw [hgc, ← hd, ← he] at h
    exact h
  have hP1 : (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e ∣
      (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs := Nat.gcd_dvd_left _ _
  have hP2 : (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e ∣ e :=
    Nat.gcd_dvd_right _ _
  have hPE : (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e ∣ E :=
    hP2.trans hEdiv
  have hzX : (((10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e : ℕ) : ℤ) ∣
      10 * A * (e : ℤ) + C * (d : ℤ) :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hP1)
  have hz10 : (((10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e : ℕ) : ℤ) ∣
      10 * A * (e : ℤ) :=
    dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hP2) _
  have hzCd : (((10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e : ℕ) : ℤ) ∣
      C * (d : ℤ) := by
    have h := dvd_sub hzX hz10
    convert h using 1
    ring
  have hPd : (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e ∣
      C.natAbs * d := by
    have hx : (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e ∣
        (C * (d : ℤ)).natAbs := Int.natAbs_dvd_natAbs.mpr hzCd
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at hx
  have hPd' : (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e ∣ d :=
    (Nat.Coprime.of_dvd_left hPE hCE.symm).dvd_of_dvd_mul_left hPd
  have hGone : (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e = 1 := by
    have h := Nat.dvd_gcd hPd' hP2
    rw [show d.gcd e = 1 from hcde] at h
    exact Nat.dvd_one.mp h
  exact hGone

private theorem excessGCD_coprime_aux (A C : ℤ) (D E H d e : ℕ)
    (hH : H = Nat.gcd D E) (hd : d = D / H) (he : e = E / H)
    (hCE : Nat.Coprime C.natAbs E) (hpos : 0 < H) :
    Nat.Coprime
      (Int.gcd (10 * A * (e : ℤ) + C * (d : ℤ)) ((H * d : ℕ) : ℤ)) e := by
  have hXcop : Nat.Coprime
      (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs e :=
    excessNumerator_coprime_aux A C D E H d e hH hd he hCE hpos
  have hP1 : Int.gcd (10 * A * (e : ℤ) + C * (d : ℤ))
      ((H * d : ℕ) : ℤ) ∣
      (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs := by
    have h := Int.gcd_dvd_left (10 * A * (e : ℤ) + C * (d : ℤ))
      ((H * d : ℕ) : ℤ)
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h)
  have h : Nat.gcd
      (Int.gcd (10 * A * (e : ℤ) + C * (d : ℤ)) ((H * d : ℕ) : ℤ)) e ∣
      Nat.gcd (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs e :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans hP1) (Nat.gcd_dvd_right _ _)
  rw [show (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs.gcd e = 1 from hXcop] at h
  exact Nat.dvd_one.mp h

private theorem decomp_aux (A C : ℤ) (D E H d e : ℕ) (X U : ℤ) (V k g : ℕ)
    (hH : H = Nat.gcd D E) (hd : d = D / H) (he : e = E / H)
    (hX : X = 10 * A * (e : ℤ) + C * (d : ℤ))
    (hU : U = 10 * A * (E : ℤ) + C * (D : ℤ))
    (hV : V = D * E) (hk : k = Int.gcd X ((H * d : ℕ) : ℤ))
    (hg : g = Int.gcd U ((V : ℕ) : ℤ))
    (hAD : Nat.Coprime A.natAbs D) (hCE : Nat.Coprime C.natAbs E) :
    U = (H : ℤ) * X ∧ V = H ^ 2 * d * e ∧ g = H * k ∧ k ∣ D ∧
      k ∣ 10 * H ∧ V / g = H * d * e / k ∧ V / g = D * e / k := by
  rcases Nat.eq_zero_or_pos H with h0 | hHpos
  · subst h0
    obtain ⟨hD0, hE0⟩ := Nat.gcd_eq_zero_iff.mp hH.symm
    subst hD0
    subst hE0
    have hd0 : d = 0 := by rw [hd]
    subst hd0
    have he0 : e = 0 := by rw [he]
    subst he0
    have hX0 : X = 0 := by rw [hX]; ring
    subst hX0
    have hU0 : U = 0 := by rw [hU]; ring
    subst hU0
    have hV0 : V = 0 := by rw [hV]
    subst hV0
    have hk0 : k = 0 := by rw [hk]; simp
    subst hk0
    have hg0 : g = 0 := by rw [hg]; simp
    subst hg0
    refine ⟨rfl, rfl, rfl, dvd_zero _, dvd_zero _, ?_, ?_⟩ <;> simp
  · have hgc : Nat.gcd D E = H := hH.symm
    have hHD : H ∣ D := by rw [← hgc]; exact Nat.gcd_dvd_left D E
    have hHE : H ∣ E := by rw [← hgc]; exact Nat.gcd_dvd_right D E
    have hDd : D = d * H := by rw [hd]; exact (Nat.div_mul_cancel hHD).symm
    have hEe : E = e * H := by rw [he]; exact (Nat.div_mul_cancel hHE).symm
    have hXe : Nat.Coprime X.natAbs e := by
      have h := excessNumerator_coprime_aux A C D E H d e hH hd he hCE hHpos
      rw [← hX] at h
      exact h
    have hUX : U = (H : ℤ) * X := by
      rw [hU, hX, hDd, hEe]
      push_cast
      ring
    have hVH : V = H * (H * d * e) := by
      rw [hV, hDd, hEe]
      ring
    have hV2 : ((V : ℕ) : ℤ) = (H : ℤ) * ((H * d * e : ℕ) : ℤ) := by
      rw [hVH, Int.natCast_mul]
    have hg1 : g = H * Int.gcd X ((H * d * e : ℕ) : ℤ) := by
      rw [hg, hUX, hV2, Int.gcd_mul_left]
      simp
    have hGk : Int.gcd X ((H * d * e : ℕ) : ℤ) =
        Int.gcd X ((H * d : ℕ) : ℤ) := by
      rw [show Int.gcd X ((H * d * e : ℕ) : ℤ) =
          Nat.gcd X.natAbs (H * d * e) from rfl,
        show Int.gcd X ((H * d : ℕ) : ℤ) = Nat.gcd X.natAbs (H * d) from rfl]
      refine Nat.dvd_antisymm ?_ ?_
      · have h1 : Nat.gcd X.natAbs (H * d * e) ∣ X.natAbs := Nat.gcd_dvd_left _ _
        have h2 : Nat.gcd X.natAbs (H * d * e) ∣ H * d * e := Nat.gcd_dvd_right _ _
        have hcop : (Nat.gcd X.natAbs (H * d * e)).Coprime e :=
          Nat.Coprime.of_dvd_left h1 hXe
        exact Nat.dvd_gcd h1 (hcop.dvd_of_dvd_mul_right h2)
      · have h1 : Nat.gcd X.natAbs (H * d) ∣ X.natAbs := Nat.gcd_dvd_left _ _
        have h2 : Nat.gcd X.natAbs (H * d) ∣ H * d := Nat.gcd_dvd_right _ _
        have h3 : Nat.gcd X.natAbs (H * d) ∣ H * d * e :=
          h2.trans (Nat.dvd_mul_right _ _)
        exact Nat.dvd_gcd h1 h3
    have hgk : g = H * k := by rw [hg1, hGk, ← hk]
    have hknHD : k ∣ H * d := by
      rw [hk]
      exact Int.natCast_dvd_natCast.mp
        (Int.gcd_dvd_right X ((H * d : ℕ) : ℤ))
    have hkD : k ∣ D := by rw [hDd, Nat.mul_comm d H]; exact hknHD
    have hkXabs : k ∣ X.natAbs := by
      rw [hk]
      exact Int.natCast_dvd_natCast.mp
        (Int.dvd_natAbs.mpr (Int.gcd_dvd_left X ((H * d : ℕ) : ℤ)))
    have hke : k.Coprime e := Nat.Coprime.of_dvd_left hkXabs hXe
    have hkA : k.Coprime A.natAbs := Nat.Coprime.of_dvd_left hkD hAD.symm
    have hzX : (k : ℤ) ∣ X := by
      rw [hk]
      exact Int.gcd_dvd_left X ((H * d : ℕ) : ℤ)
    have hzU : (k : ℤ) ∣ U := by
      rw [hUX]
      exact hzX.trans (dvd_mul_left X (H : ℤ))
    have hzD : (k : ℤ) ∣ (D : ℤ) := by
      rw [hDd, Nat.mul_comm d H]
      exact Int.natCast_dvd_natCast.mpr hknHD
    have hz10AE : (k : ℤ) ∣ 10 * A * (E : ℤ) := by
      have h := dvd_sub hzU (dvd_mul_of_dvd_right hzD C)
      rw [hUX, hX] at h
      have h2 : (H : ℤ) * (10 * A * (e : ℤ) + C * (d : ℤ)) -
          C * (D : ℤ) = 10 * A * (E : ℤ) := by
        rw [hDd, hEe]
        push_cast
        ring
      rw [h2] at h
      exact h
    have hk10AE : k ∣ 10 * A.natAbs * E := by
      have hx : k ∣ (10 * A * (E : ℤ)).natAbs :=
        Int.natAbs_dvd_natAbs.mpr hz10AE
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast] at hx
      norm_num at hx
      exact hx
    have hid : 10 * A.natAbs * (e * H) = 10 * H * (A.natAbs * e) := by ring
    have hk10 : k ∣ 10 * H := by
      rw [hEe, hid] at hk10AE
      exact (Nat.Coprime.mul_right hkA hke).dvd_of_dvd_mul_right hk10AE
    have hidQ : D * e = H * d * e := by rw [hDd]; ring
    have hVsq : V = H ^ 2 * d * e := by rw [hVH]; ring
    refine ⟨hUX, hVsq, hgk, hkD, hk10, ?_, ?_⟩
    · rw [hVH, hgk, Nat.mul_div_mul_left _ _ hHpos]
    · rw [hVH, hgk, Nat.mul_div_mul_left _ _ hHpos, hidQ]

/-- The excess numerator is coprime to the second reduced denominator. -/
theorem excessNumerator_coprime_rightQuotient :
    ∀ (A C : ℤ) (D E : ℕ), Nat.Coprime C.natAbs E → 0 < Nat.gcd D E →
    (let H : ℕ := Nat.gcd D E; let d : ℕ := D / H; let e : ℕ := E / H;
      Nat.Coprime (10 * A * (e : ℤ) + C * (d : ℤ)).natAbs e) :=
  fun A C D E hCE hpos =>
    excessNumerator_coprime_aux A C D E _ _ _ rfl rfl rfl hCE hpos

/-- The excess gcd is coprime to the second reduced denominator. -/
theorem excessGCD_coprime_rightQuotient :
    ∀ (A C : ℤ) (D E : ℕ), Nat.Coprime C.natAbs E → 0 < Nat.gcd D E →
    (let H : ℕ := Nat.gcd D E; let d : ℕ := D / H; let e : ℕ := E / H;
      Nat.Coprime
        (Int.gcd (10 * A * (e : ℤ) + C * (d : ℤ)) ((H * d : ℕ) : ℤ)) e) :=
  fun A C D E hCE hpos =>
    excessGCD_coprime_aux A C D E _ _ _ rfl rfl rfl hCE hpos

/-- Exact common-denominator and excess-gcd decomposition, including zero denominators. -/
theorem reducedCrossSum_excessGCD_decomposition :
    ∀ (A C : ℤ) (D E : ℕ), Nat.Coprime A.natAbs D →
      Nat.Coprime C.natAbs E →
    (let H : ℕ := Nat.gcd D E; let d : ℕ := D / H; let e : ℕ := E / H;
      let X : ℤ := 10 * A * (e : ℤ) + C * (d : ℤ);
      let U : ℤ := 10 * A * (E : ℤ) + C * (D : ℤ);
      let V : ℕ := D * E; let k : ℕ := Int.gcd X ((H * d : ℕ) : ℤ);
      let g : ℕ := Int.gcd U (V : ℤ);
      U = (H : ℤ) * X ∧ V = H ^ 2 * d * e ∧ g = H * k ∧ k ∣ D ∧
        k ∣ 10 * H ∧ V / g = H * d * e / k ∧ V / g = D * e / k) := by
  intro A C D E hAD hCE
  exact decomp_aux A C D E _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl hAD hCE

end Theory.PiDigits.T117CommonDenominatorExcessGCD
