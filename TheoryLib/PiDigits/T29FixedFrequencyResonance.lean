import TheoryLib.PiDigits.T20BaseTenOrbitDensity
import TheoryLib.PiDigits.T27FiniteExponentialCylinderCoverage

/-!
# Fixed-frequency resonance forced by failure of decimal disjunctivity

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file proves only a necessary resonance consequence of a missing finite
word in T7's exact decimal digit stream. It proves neither canonical V1 nor
the sibling statement V3, and it does not prove that either statement fails.
The quantitative input is T27's proved decimal-cylinder deficit inequality,
used through T27's coverage corollary.
-/

noncomputable section

open Filter Finset Set
open scoped ComplexConjugate Real Topology

namespace Theory.PiDigits.T29

/-- Concrete frequency cutoff for words of length `k`. -/
def H (k : ℕ) : ℕ := 2 * 10 ^ (2 * k)

/-- Concrete positive linear resonance margin for words of length `k`. -/
def epsilon (k : ℕ) : ℝ := (8 * (10 : ℝ) ^ (2 * k))⁻¹

/-- The raw, unnormalized exponential sum requested by the analytic
formulation, before taking fractional parts. -/
def piExponentialSum (N : ℕ) (h : ℤ) : ℂ :=
  ∑ j ∈ range N,
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
        ((((10 : ℝ) ^ j * Real.pi : ℝ)) : ℂ))

/-- A finite word is absent from T7's exact floor-based decimal stream. -/
def WordMissing (s : List (Fin 10)) : Prop :=
  ∀ n : ℕ, ¬ ∀ i : ℕ, ∀ hi : i < s.length,
    Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩

lemma H_pos (k : ℕ) : 0 < H k := by
  simp [H]

lemma epsilon_pos (k : ℕ) : 0 < epsilon k := by
  simp [epsilon]

lemma phase_fract_eq_phase (h : ℤ) (x : ℝ) :
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
          ((Int.fract x : ℝ) : ℂ)) =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (x : ℂ)) := by
  rw [Int.fract]
  rw [show
    2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
          ((x - (⌊x⌋ : ℤ) : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (x : ℂ) +
          ((-⌊x⌋ * h : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma piFractional_exponentialSum_eq (N : ℕ) (h : ℤ) :
    Theory.PiDigits.T27.exponentialSum
        Theory.PiDigits.T27.piFractionalOrbit N h =
      piExponentialSum N h := by
  classical
  apply sum_congr rfl
  intro j hj
  change Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
        ((Int.fract ((10 : ℝ) ^ j * Real.pi) : ℝ) : ℂ)) = _
  exact phase_fract_eq_phase h ((10 : ℝ) ^ j * Real.pi)

lemma certificateCoefficient_lt_one (k : ℕ) :
    (H k : ℝ) * epsilon k +
        1 / (((H k : ℝ) + 1) *
          Theory.PiDigits.T27.decimalCylinderLength k ^ 2) < 1 := by
  let q : ℝ := (10 : ℝ) ^ (2 * k)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hH : (H k : ℝ) = 2 * q := by
    dsimp [H, q]
    push_cast
    ring
  have hepsilon : epsilon k = (8 * q)⁻¹ := by
    rfl
  have hL : Theory.PiDigits.T27.decimalCylinderLength k ^ 2 = q⁻¹ := by
    dsimp [Theory.PiDigits.T27.decimalCylinderLength, q]
    rw [inv_pow, ← pow_mul]
    congr 2
    omega
  rw [hH, hepsilon, hL]
  change 2 * q * (8 * q)⁻¹ + 1 / ((2 * q + 1) * q⁻¹) < 1
  have hfirst : 2 * q * (8 * q)⁻¹ = (1 : ℝ) / 4 := by
    field_simp
    norm_num
  have hden : 0 < 2 * q + 1 := by positivity
  have hsecond : 1 / ((2 * q + 1) * q⁻¹) < (1 : ℝ) / 2 := by
    have heq : 1 / ((2 * q + 1) * q⁻¹) = q / (2 * q + 1) := by
      field_simp
    rw [heq]
    apply (div_lt_iff₀ hden).2
    linarith
  rw [hfirst]
  linarith

/-- For every positive prefix length, omission of `s` forces one of the
explicitly bounded nonzero frequencies to have a linear-size raw sum. -/
theorem exists_frequency_resonance_at_length_of_wordMissing
    (s : List (Fin 10)) (hmissing : WordMissing s) (N : ℕ) (hN : 0 < N) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ H s.length ∧
      epsilon s.length * (N : ℝ) < ‖piExponentialSum N h‖ := by
  by_contra hno
  have hbound : Theory.PiDigits.T27.FirstFrequencyBound
      Theory.PiDigits.T27.piFractionalOrbit N (H s.length)
        (epsilon s.length * (N : ℝ)) := by
    intro h h0 hH
    rw [piFractional_exponentialSum_eq]
    exact le_of_not_gt fun hlarge => hno ⟨h, h0, hH, hlarge⟩
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcertificate :
      (H s.length : ℝ) * (epsilon s.length * (N : ℝ)) +
          (N : ℝ) *
            (1 / (((H s.length : ℝ) + 1) *
              Theory.PiDigits.T27.decimalCylinderLength s.length ^ 2)) <
        (N : ℝ) := by
    calc
      (H s.length : ℝ) * (epsilon s.length * (N : ℝ)) +
            (N : ℝ) *
              (1 / (((H s.length : ℝ) + 1) *
                Theory.PiDigits.T27.decimalCylinderLength s.length ^ 2)) =
          (N : ℝ) *
            ((H s.length : ℝ) * epsilon s.length +
              1 / (((H s.length : ℝ) + 1) *
                Theory.PiDigits.T27.decimalCylinderLength s.length ^ 2)) := by
            ring
      _ < (N : ℝ) * 1 := mul_lt_mul_of_pos_left
        (certificateCoefficient_lt_one s.length) hNR
      _ = (N : ℝ) := mul_one _
  obtain ⟨n, hnN, hnmem⟩ :=
    Theory.PiDigits.T27.decimalCylinder_covered_of_firstFrequencyBound
      Theory.PiDigits.T27.piFractionalOrbit N (H s.length) hN
      (Theory.PiDigits.T27.decimalCylinderLeft s)
      (Theory.PiDigits.T27.decimalCylinderLength s.length)
      (epsilon s.length * (N : ℝ))
      (fun j _hj => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (Theory.PiDigits.T27.decimalCylinderLength_pos s.length)
      (Theory.PiDigits.T27.decimalCylinderRight_le_one s)
      hbound hcertificate
  rw [Theory.PiDigits.T27.decimalCylinder_interval] at hnmem
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
    s (Theory.PiDigits.T27.piFractionalOrbit n) hnmem
  apply hmissing n
  intro i hi
  have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
    Real.pi Real.pi_pos.le n i
  exact (Theory.PiDigits.T20.decimalDigit_pi (n + i)).symm.trans
    (hshift.symm.trans (hdigits i hi))

/-- The finite set of nonzero integer frequencies with absolute value at most
`K`. -/
def boundedFrequencies (K : ℕ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter fun h => h ≠ 0

lemma mem_boundedFrequencies_iff {K : ℕ} {h : ℤ} :
    h ∈ boundedFrequencies K ↔ h ≠ 0 ∧ h.natAbs ≤ K := by
  simp only [boundedFrequencies, mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, h0⟩
    refine ⟨h0, ?_⟩
    cases h <;> simp at * <;> omega
  · rintro ⟨h0, habs⟩
    refine ⟨?_, h0⟩
    cases h <;> simp at * <;> omega

/-- A finite pigeonhole principle in the exact `forall threshold, exists
later index` form used to fix the frequency before choosing prefix lengths. -/
lemma Finset.exists_fixed_of_forall_exists_ge
    {α : Type*} (S : Finset α) (P : α → ℕ → Prop)
    (h : ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧ ∃ a ∈ S, P a N) :
    ∃ a ∈ S, ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧ P a N := by
  have hfrequent : ∃ᶠ N in atTop, ∃ a ∈ S, P a N :=
    frequently_atTop.mpr h
  obtain ⟨a, haS, ha⟩ := S.frequently_exists.mp hfrequent
  exact ⟨a, haS, fun B => ha.forall_exists_of_atTop B⟩

/-- A fixed missing nonempty `k`-digit word forces one fixed bounded nonzero
integer frequency to resonate along arbitrarily large prefixes. The frequency
is chosen before the threshold. -/
theorem fixed_frequency_resonance_of_wordMissing
    (k : ℕ) (s : List (Fin 10)) (hs : s.length = k) (_hk : 0 < k)
    (hmissing : WordMissing s) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ H k ∧
      ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧
        epsilon k * (N : ℝ) ≤ ‖piExponentialSum N h‖ := by
  let S := boundedFrequencies (H k)
  let P : ℤ → ℕ → Prop := fun h N =>
    epsilon k * (N : ℝ) ≤ ‖piExponentialSum N h‖
  have hunbounded : ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧ ∃ h ∈ S, P h N := by
    intro B
    let N := max 1 B
    have hN : 0 < N := by
      dsimp [N]
      omega
    obtain ⟨h, h0, hH, hlarge⟩ :=
      exists_frequency_resonance_at_length_of_wordMissing s hmissing N hN
    refine ⟨N, ?_, h, ?_, ?_⟩
    · dsimp [N]
      omega
    · rw [mem_boundedFrequencies_iff]
      exact ⟨h0, by simpa only [hs] using hH⟩
    · dsimp [P]
      simpa only [hs] using hlarge.le
  obtain ⟨h, hhS, hfrequent⟩ :=
    Finset.exists_fixed_of_forall_exists_ge S P hunbounded
  rw [mem_boundedFrequencies_iff] at hhS
  exact ⟨h, hhS.1, hhS.2, hfrequent⟩

/-- Exact T7 specialization: the literal negation of canonical V1 implies a
fixed-frequency resonance obstruction. This is a necessary consequence of
V1 failure only; it proves neither V1 nor V3 and does not establish `¬ V1`. -/
theorem not_canonicalV1_implies_fixed_frequency_resonance
    (hnot : ¬ Theory.PiDigits.V1) :
    ∃ k : ℕ, 0 < k ∧ ∃ s : List (Fin 10), s.length = k ∧
      WordMissing s ∧
      ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ H k ∧
        ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧
          epsilon k * (N : ℝ) ≤ ‖piExponentialSum N h‖ := by
  have hexists : ∃ s : List (Fin 10), WordMissing s := by
    by_contra hnone
    apply hnot
    intro s
    by_contra hs
    apply hnone
    refine ⟨s, ?_⟩
    intro n hn
    exact hs ⟨n, hn⟩
  obtain ⟨s, hmissing⟩ := hexists
  have hspos : 0 < s.length := by
    apply Nat.pos_of_ne_zero
    intro hs0
    apply hmissing 0
    intro i hi
    omega
  obtain ⟨h, h0, hH, hres⟩ :=
    fixed_frequency_resonance_of_wordMissing
      s.length s rfl hspos hmissing
  exact ⟨s.length, hspos, s, rfl, hmissing, h, h0, hH, hres⟩

end Theory.PiDigits.T29

#print axioms Theory.PiDigits.T29.exists_frequency_resonance_at_length_of_wordMissing
#print axioms Theory.PiDigits.T29.Finset.exists_fixed_of_forall_exists_ge
#print axioms Theory.PiDigits.T29.fixed_frequency_resonance_of_wordMissing
#print axioms Theory.PiDigits.T29.not_canonicalV1_implies_fixed_frequency_resonance
