import TheoryLib.PiQuantitativeBlockHitting.T117T117CommonDenominatorExcessGCD

/-!
# T118: pointwise normalized-excess cell interval for the sampled BBP successor

For each `N`, the actual reduced rationals `Q = 10^N * bbpPartial (7*N)` and
`F = sampledBBPForcingRat N` have signed numerators `A, C` and positive
denominators `D, E`.  With `H = gcd D E`, `d = D/H`, `e = E/H`,
`X = 10*A*e + C*d`, `k = gcd X (H*d)` and `W = H*d*e/k`, the sampled BBP
successor `10^(N+1) * bbpPartial (7*(N+1))` has signed numerator `X/k` and
positive denominator `W` (T117 removes the common factor `H` from the T114
pair; nothing is assumed about cancellation beyond that exact identity).

Consequences recorded here, all purely pointwise:

* the Euclidean remainder `R = (X/k) % W` satisfies `0 <= R < W`;
* the cyclic cell of the successor equals `(q*R/W : ZMod q)`;
* for `0 < q` and `a < q`, the successor cell equals `a` exactly when
  `a*W <= q*R < (a+1)*W` (half-open, endpoint-exact).

No existence, recurrence, occupancy, density, cancellation, normality,
digit-occurrence, or V1 statement is made.
-/

namespace Theory.PiDigits.T118SampledBBPNormalizedExcessCell

open Theory.PiDigits.T106BBPForcedOrbit Theory.PiDigits.T77SelectedPadicDefectShell

/-- Standalone restatement of T113's cell formula with the `let` expanded. -/
private theorem orbit_cell_eq (q N : ℕ) :
    DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (sampledBBPOrbit N) =
      ((((q : ℤ) *
          (((10 : ℚ) ^ N * bbpPartial (7 * N)).num %
            (((10 : ℚ) ^ N * bbpPartial (7 * N)).den : ℤ))) /
        (((10 : ℚ) ^ N * bbpPartial (7 * N)).den : ℤ) : ℤ) : ZMod q) :=
  Theory.PiDigits.T113SampledBBPReducedCellRecurrence.cyclicCell_sampledBBPOrbit_eq_selectedCell
    q N

/-- Core computation: the actual sampled BBP successor pair, normalized by the
excess gcd, together with positivity of `k` and `W`. -/
private theorem core_num_den_pos (N : ℕ) (Q F : ℚ) (H d e k W : ℕ) (X : ℤ)
    (hQ : Q = (10 : ℚ) ^ N * bbpPartial (7 * N))
    (hF : F = sampledBBPForcingRat N)
    (hH : H = Nat.gcd Q.den F.den)
    (hd : d = Q.den / H) (he : e = F.den / H)
    (hX : X = 10 * Q.num * (e : ℤ) + F.num * (d : ℤ))
    (hk : k = Int.gcd X ((H * d : ℕ) : ℤ))
    (hW : W = H * d * e / k)
    (hAD : Nat.Coprime Q.num.natAbs Q.den)
    (hCE : Nat.Coprime F.num.natAbs F.den) :
    ((10 : ℚ) ^ (N + 1) * bbpPartial (7 * (N + 1))).num = X / (k : ℤ) ∧
      ((10 : ℚ) ^ (N + 1) * bbpPartial (7 * (N + 1))).den = W ∧
      0 < k ∧ 0 < W := by
  have hDpos : 0 < Q.den := Rat.den_pos Q
  have hEpos : 0 < F.den := Rat.den_pos F
  have hHpos : 0 < H := by rw [hH]; exact Nat.gcd_pos_of_pos_left _ hDpos
  have hHD : H ∣ Q.den := by rw [hH]; exact Nat.gcd_dvd_left Q.den F.den
  have hHE : H ∣ F.den := by rw [hH]; exact Nat.gcd_dvd_right Q.den F.den
  have hdpos : 0 < d := by
    rw [hd]
    exact Nat.div_pos (Nat.le_of_dvd hDpos hHD) hHpos
  have hepos : 0 < e := by
    rw [he]
    exact Nat.div_pos (Nat.le_of_dvd hEpos hHE) hHpos
  have hHdpos : 0 < H * d := Nat.mul_pos hHpos hdpos
  have hkpos : 0 < k := by
    rw [hk]
    exact Int.gcd_pos_of_ne_zero_right X (by
      have : (0 : ℤ) < ((H * d : ℕ) : ℤ) := by exact_mod_cast hHdpos
      exact ne_of_gt this)
  -- T117: remove the common-denominator factor `H` from the T114 pair.
  obtain ⟨hUX, -, hgk, -, -, hVgW, -⟩ :=
    Theory.PiDigits.T117CommonDenominatorExcessGCD.reducedCrossSum_excessGCD_decomposition
      Q.num F.num Q.den F.den hAD hCE
  rw [← hH, ← hd, ← he] at hUX hgk hVgW
  rw [← hX] at hUX hgk hVgW
  rw [← hk] at hgk hVgW
  -- T114: the actual successor pair before removing `H`.
  obtain ⟨hsnum, hsden⟩ :=
    Theory.PiDigits.T114SampledBBPGCDNormalizedSuccessor.scaledBBPPartialRat_succ_num_den N
  rw [← hQ, ← hF] at hsnum hsden
  refine ⟨?_, ?_, hkpos, ?_⟩
  · rw [hsnum]
    have hkz : (k : ℤ) ∣ X := by
      rw [hk]
      exact Int.gcd_dvd_left X _
    have hc : (k : ℤ) * (X / (k : ℤ)) = X := by
      rw [Int.mul_comm]
      exact Int.ediv_mul_cancel hkz
    refine Int.ediv_eq_of_eq_mul_left ?_ ?_
    · rw [hgk]
      push_cast
      exact mul_ne_zero (by exact_mod_cast ne_of_gt hHpos)
        (by exact_mod_cast ne_of_gt hkpos)
    · rw [hgk, hUX]
      push_cast
      calc (H : ℤ) * X = (H : ℤ) * ((k : ℤ) * (X / (k : ℤ))) := by rw [hc]
        _ = X / (k : ℤ) * ((H : ℤ) * (k : ℤ)) := by ring
  · rw [hsden, hVgW]
    exact hW.symm
  · have hkd : k ∣ H * d := by
      rw [hk]
      exact Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right X _)
    have h2 : k * e ≤ H * d * e :=
      Nat.mul_le_mul_right e (Nat.le_of_dvd hHdpos hkd)
    have h3 : e * k ≤ H * d * e := by
      rw [Nat.mul_comm e k]
      exact h2
    rw [hW]
    calc 1 ≤ e := hepos
      _ = e * k / k := by rw [Nat.mul_div_cancel e hkpos]
      _ ≤ H * d * e / k := Nat.div_le_div_right h3

/-- Endpoint-exact half-open characterization of a `ZMod q` cell representative. -/
private theorem zmod_cell_iff (q a W : ℕ) (R : ℤ) {n : ℤ} (_hn : n = (q : ℤ) * R / (W : ℤ)) (hq : 0 < q) (haq : a < q)
    (hWpos : 0 < W) (hRlo : 0 ≤ R) (hRhi : R < (W : ℤ)) :
    ((((q : ℤ) * R) / (W : ℤ) : ℤ) : ZMod q) = (a : ZMod q) ↔
      (a : ℤ) * (W : ℤ) ≤ (q : ℤ) * R ∧
        (q : ℤ) * R < ((a + 1 : ℕ) : ℤ) * (W : ℤ) := by
  subst _hn
  have hwz : (W : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hWpos
  have hqz : 0 < (q : ℤ) := by exact_mod_cast hq
  have hqr0 : 0 ≤ (q : ℤ) * R := Int.mul_nonneg hqz.le hRlo
  have hn0 : 0 ≤ (q : ℤ) * R / (W : ℤ) :=
    Int.ediv_nonneg hqr0 (by exact_mod_cast Nat.zero_le W)
  have hqrw : (q : ℤ) * R < (q : ℤ) * (W : ℤ) :=
    Int.mul_lt_mul_of_pos_left hRhi hqz
  have hnq : (q : ℤ) * R / (W : ℤ) < (q : ℤ) :=
    (Int.ediv_lt_iff_lt_mul (by exact_mod_cast hWpos)).mpr hqrw
  have hsplit : (q : ℤ) * R =
      (W : ℤ) * ((q : ℤ) * R / (W : ℤ)) + (q : ℤ) * R % (W : ℤ) :=
    (Int.mul_ediv_add_emod _ _).symm
  have hr'lo : 0 ≤ (q : ℤ) * R % (W : ℤ) := Int.emod_nonneg _ hwz
  have hr'hi : (q : ℤ) * R % (W : ℤ) < (W : ℤ) :=
    Int.emod_lt_of_pos _ (by exact_mod_cast hWpos)
  have hmodself : (q : ℤ) * R / (W : ℤ) % (q : ℤ) = (q : ℤ) * R / (W : ℤ) :=
    Int.emod_eq_of_lt hn0 hnq
  have hcastA : ((a : ZMod q)) = (((a : ℤ) : ZMod q)) := by
    try rfl
    simp only [Int.cast_natCast]
  constructor
  · intro heq
    rw [hcastA, ZMod.intCast_eq_intCast_iff'] at heq
    have hamod : (a : ℤ) % (q : ℤ) = (a : ℤ) :=
      Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le a) (by exact_mod_cast haq)
    rw [hamod, hmodself] at heq
    have hndiv : (q : ℤ) * R / (W : ℤ) = (a : ℤ) := heq
    have hjoin : (q : ℤ) * R = (W : ℤ) * (a : ℤ) + (q : ℤ) * R % (W : ℤ) := by
      calc (q : ℤ) * R =
          (W : ℤ) * ((q : ℤ) * R / (W : ℤ)) + (q : ℤ) * R % (W : ℤ) := hsplit
        _ = (W : ℤ) * (a : ℤ) + (q : ℤ) * R % (W : ℤ) := by rw [hndiv]
    constructor
    · calc (a : ℤ) * (W : ℤ) = (W : ℤ) * (a : ℤ) := Int.mul_comm _ _
      _ ≤ (W : ℤ) * (a : ℤ) + (q : ℤ) * R % (W : ℤ) := le_add_of_nonneg_right hr'lo
      _ = (q : ℤ) * R := hjoin.symm
    · calc (q : ℤ) * R = (W : ℤ) * (a : ℤ) + (q : ℤ) * R % (W : ℤ) := hjoin
      _ < (W : ℤ) * (a : ℤ) + (W : ℤ) := by linarith
      _ = ((a + 1 : ℕ) : ℤ) * (W : ℤ) := by push_cast; ring
  · rintro ⟨hle, hlt⟩
    have hale : (a : ℤ) ≤ (q : ℤ) * R / (W : ℤ) :=
      (Int.le_ediv_iff_mul_le (by exact_mod_cast hWpos)).mpr hle
    have halt : (q : ℤ) * R / (W : ℤ) < (a : ℤ) + 1 :=
      (Int.ediv_lt_iff_lt_mul (by exact_mod_cast hWpos)).mpr hlt
    have heq : (q : ℤ) * R / (W : ℤ) = (a : ℤ) := by omega
    rw [heq, hcastA]

/-- **Frozen statement 1.** The sampled BBP successor has normalized signed
numerator `X/k`, positive reduced denominator `W`, and `0 < k`, `0 < W`. -/
theorem sampledBBPSuccessor_normalizedExcess_num_den_pos (N : ℕ) :
    (let Q : ℚ := (10 : ℚ) ^ N *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N);
      let F : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N;
      let H : ℕ := Nat.gcd Q.den F.den;
      let d : ℕ := Q.den / H;
      let e : ℕ := F.den / H;
      let X : ℤ := 10 * Q.num * (e : ℤ) + F.num * (d : ℤ);
      let k : ℕ := Int.gcd X ((H * d : ℕ) : ℤ);
      let W : ℕ := H * d * e / k;
      let S : ℚ := (10 : ℚ) ^ (N + 1) *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * (N + 1));
      S.num = X / (k : ℤ) ∧ S.den = W ∧ 0 < k ∧ 0 < W) := by
  intro Q F H d e X k W S
  exact core_num_den_pos N Q F H d e k W X rfl rfl rfl rfl rfl rfl rfl rfl
    Q.reduced F.reduced

/-- **Frozen statement 2.** The Euclidean remainder `R` of the normalized
signed numerator lies in `[0, W)`. -/
theorem normalizedExcessRemainder_bounds (N : ℕ) :
    (let Q : ℚ := (10 : ℚ) ^ N *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N);
      let F : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N;
      let H : ℕ := Nat.gcd Q.den F.den;
      let d : ℕ := Q.den / H;
      let e : ℕ := F.den / H;
      let X : ℤ := 10 * Q.num * (e : ℤ) + F.num * (d : ℤ);
      let k : ℕ := Int.gcd X ((H * d : ℕ) : ℤ);
      let W : ℕ := H * d * e / k;
      let R : ℤ := (X / (k : ℤ)) % (W : ℤ);
      0 ≤ R ∧ R < (W : ℤ)) := by
  intro Q F H d e X k W R
  have hcore := core_num_den_pos N Q F H d e k W X rfl rfl rfl rfl rfl rfl rfl rfl
    Q.reduced F.reduced
  have hkpos := hcore.2.2.1
  have hwpos := hcore.2.2.2
  have hwz : (W : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hwpos
  exact ⟨Int.emod_nonneg _ hwz, Int.emod_lt_of_pos _ (by exact_mod_cast hwpos)⟩

/-- **Frozen statement 3.** The cyclic cell of the sampled BBP successor has
the exact normalized-excess quotient formula. -/
theorem cyclicCell_sampledBBPOrbit_succ_eq_normalizedExcess (q N : ℕ) :
    (let Q : ℚ := (10 : ℚ) ^ N *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N);
      let F : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N;
      let H : ℕ := Nat.gcd Q.den F.den;
      let d : ℕ := Q.den / H;
      let e : ℕ := F.den / H;
      let X : ℤ := 10 * Q.num * (e : ℤ) + F.num * (d : ℤ);
      let k : ℕ := Int.gcd X ((H * d : ℕ) : ℤ);
      let W : ℕ := H * d * e / k;
      DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
          (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit (N + 1)) =
        ((((((q : ℤ) * ((X / (k : ℤ)) % (W : ℤ))) / (W : ℤ) : ℤ)) : ZMod q))) := by
  intro Q F H d e X k W
  have hcore := core_num_den_pos N Q F H d e k W X rfl rfl rfl rfl rfl rfl rfl rfl
    Q.reduced F.reduced
  rw [orbit_cell_eq, hcore.1, hcore.2.1]

/-- **Frozen statement 4.** For `0 < q` and `a < q`, equality with the cell
`a` is equivalent to the endpoint-exact half-open integer interval. -/
theorem sampledBBPSuccessor_cell_eq_iff_normalizedExcess_interval (N q a : ℕ)
    (hq : 0 < q) (haq : a < q) :
    (let Q : ℚ := (10 : ℚ) ^ N *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N);
      let F : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N;
      let H : ℕ := Nat.gcd Q.den F.den;
      let d : ℕ := Q.den / H;
      let e : ℕ := F.den / H;
      let X : ℤ := 10 * Q.num * (e : ℤ) + F.num * (d : ℤ);
      let k : ℕ := Int.gcd X ((H * d : ℕ) : ℤ);
      let W : ℕ := H * d * e / k;
      let R : ℤ := (X / (k : ℤ)) % (W : ℤ);
      DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
          (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit (N + 1)) = (a : ZMod q) ↔
        (a : ℤ) * (W : ℤ) ≤ (q : ℤ) * R ∧
          (q : ℤ) * R < ((a + 1 : ℕ) : ℤ) * (W : ℤ)) := by
  intro Q F H d e X k W R
  have hcore := core_num_den_pos N Q F H d e k W X rfl rfl rfl rfl rfl rfl rfl rfl
    Q.reduced F.reduced
  have hwpos := hcore.2.2.2
  have hwz : (W : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hwpos
  have hRlo : 0 ≤ R := Int.emod_nonneg _ hwz
  have hRhi : R < (W : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hwpos)
  rw [
    show DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit (N + 1)) =
        ((((((q : ℤ) * R) / (W : ℤ) : ℤ)) : ZMod q)) from
      cyclicCell_sampledBBPOrbit_succ_eq_normalizedExcess q N]
  exact zmod_cell_iff q a W R rfl hq haq hwpos hRlo hRhi

end Theory.PiDigits.T118SampledBBPNormalizedExcessCell
