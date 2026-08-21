import TheoryLib.PiQuantitativeBlockHitting.T24T24FiniteWindowAdditiveDivergence

/-!
# T25: exact power-of-ten frequency shift for the pi orbit

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

Multiplying a Fourier frequency by `10^t` merely shifts the decimal orbit by
`t` places.  This file records the resulting exact boundary identity and its
elementary consequence: the additive Fourier gaps at frequencies `h`
and `10^t h` differ by at most `2t`, uniformly in the prefix length.

Thus the power-of-ten relation transports additive divergence but cannot by
itself amplify it to the relative cancellation required by T19.  No decimal
disjunctivity or normality conclusion is asserted here.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.PowerTenFrequencyShift

abbrev phase := Theory.PiDigits.T27.phase
abbrev exponentialSum := Theory.PiDigits.T27.exponentialSum
abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- Multiplication of the frequency by `10^t` is pointwise the same as
advancing the decimal pi orbit by `t` iterates. -/
lemma piOrbit_phase_powTen_frequency (t j : ℕ) (h : ℤ) :
    phase ((10 : ℤ) ^ t * h) (piOrbit j) =
      phase h (piOrbit (j + t)) := by
  unfold phase Theory.PiDigits.T27.phase piOrbit
    Theory.PiDigits.T27.piFractionalOrbit
  rw [Theory.PiDigits.T29.phase_fract_eq_phase ((10 : ℤ) ^ t * h)
      ((10 : ℝ) ^ j * Real.pi),
    Theory.PiDigits.T29.phase_fract_eq_phase h
      ((10 : ℝ) ^ (j + t) * Real.pi)]
  congr 1
  rw [pow_add]
  push_cast
  ring

/-- Frequency shifting rewrites the whole prefix as a shifted orbit sum. -/
lemma pi_exponentialSum_powTen_frequency (N t : ℕ) (h : ℤ) :
    exponentialSum piOrbit N ((10 : ℤ) ^ t * h) =
      ∑ j ∈ range N, phase h (piOrbit (j + t)) := by
  apply sum_congr rfl
  intro j _hj
  exact piOrbit_phase_powTen_frequency t j h

/-- Exact two-boundary identity.  Both sides are decompositions of the same
length-`N+t` orbit sum, once from the left and once from the right. -/
theorem pi_exponentialSum_powTen_frequency_add_boundary
    (N t : ℕ) (h : ℤ) :
    exponentialSum piOrbit N ((10 : ℤ) ^ t * h) +
        exponentialSum piOrbit t h =
      exponentialSum piOrbit N h +
        ∑ j ∈ range t, phase h (piOrbit (N + j)) := by
  rw [pi_exponentialSum_powTen_frequency]
  unfold exponentialSum Theory.PiDigits.T27.exponentialSum
  rw [add_comm (∑ j ∈ range N, phase h (piOrbit (j + t)))]
  calc
    (∑ j ∈ range t, phase h (piOrbit j)) +
          ∑ j ∈ range N, phase h (piOrbit (j + t)) =
        ∑ j ∈ range (t + N), phase h (piOrbit j) := by
          rw [sum_range_add]
          simp only [Nat.add_comm]
    _ = ∑ j ∈ range (N + t), phase h (piOrbit j) := by
          rw [Nat.add_comm]
    _ = (∑ j ∈ range N, phase h (piOrbit j)) +
          ∑ j ∈ range t, phase h (piOrbit (N + j)) := by
          rw [sum_range_add]

/-- A finite phase sum is bounded by the number of terms. -/
lemma norm_sum_phase_range_le (n start : ℕ) (h : ℤ) :
    ‖∑ j ∈ range n, phase h (piOrbit (start + j))‖ ≤ n := by
  calc
    ‖∑ j ∈ range n, phase h (piOrbit (start + j))‖ ≤
        ∑ j ∈ range n, ‖phase h (piOrbit (start + j))‖ :=
      norm_sum_le _ _
    _ = n := by simp [Theory.PiDigits.T27.norm_phase]

/-- The two frequency-shifted prefix sums differ by at most the two boundary
pieces, each of length `t`. -/
theorem norm_pi_exponentialSum_powTen_sub_le (N t : ℕ) (h : ℤ) :
    ‖exponentialSum piOrbit N ((10 : ℤ) ^ t * h) -
        exponentialSum piOrbit N h‖ ≤ 2 * t := by
  have hid := pi_exponentialSum_powTen_frequency_add_boundary N t h
  have hrearrange :
      exponentialSum piOrbit N ((10 : ℤ) ^ t * h) -
          exponentialSum piOrbit N h =
        (∑ j ∈ range t, phase h (piOrbit (N + j))) -
          exponentialSum piOrbit t h := by
    linear_combination hid
  rw [hrearrange]
  calc
    ‖(∑ j ∈ range t, phase h (piOrbit (N + j))) -
          exponentialSum piOrbit t h‖ ≤
        ‖∑ j ∈ range t, phase h (piOrbit (N + j))‖ +
          ‖exponentialSum piOrbit t h‖ := norm_sub_le _ _
    _ ≤ t + t := by
      apply add_le_add
      · exact norm_sum_phase_range_le t N h
      · simpa only [zero_add] using norm_sum_phase_range_le t 0 h
    _ = 2 * t := by ring

/-- Consequently, the additive gaps at `h` and `10^t h` differ by at most
`2t`, independently of `N`. -/
theorem abs_additiveGap_powTen_sub_le (N t : ℕ) (h : ℤ) :
    |((N : ℝ) - ‖exponentialSum piOrbit N ((10 : ℤ) ^ t * h)‖) -
        ((N : ℝ) - ‖exponentialSum piOrbit N h‖)| ≤ 2 * t := by
  have hnorm := abs_norm_sub_norm_le
    (exponentialSum piOrbit N ((10 : ℤ) ^ t * h))
    (exponentialSum piOrbit N h)
  have hdiff := norm_pi_exponentialSum_powTen_sub_le N t h
  calc
    |((N : ℝ) - ‖exponentialSum piOrbit N ((10 : ℤ) ^ t * h)‖) -
          ((N : ℝ) - ‖exponentialSum piOrbit N h‖)| =
        |‖exponentialSum piOrbit N h‖ -
          ‖exponentialSum piOrbit N ((10 : ℤ) ^ t * h)‖| := by ring_nf
    _ = |‖exponentialSum piOrbit N ((10 : ℤ) ^ t * h)‖ -
          ‖exponentialSum piOrbit N h‖| := abs_sub_comm _ _
    _ ≤ ‖exponentialSum piOrbit N ((10 : ℤ) ^ t * h) -
          exponentialSum piOrbit N h‖ := hnorm
    _ ≤ 2 * t := hdiff

end Theory.PiDigits.PowerTenFrequencyShift
