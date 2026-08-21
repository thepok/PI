import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc
import TheoryLib.PiLongLagBlockCollisionDecay.T76T76VariablePhasePooledHalfArc
import TheoryLib.PiLongLagBlockCollisionDecay.T81T81AdjacentIndexPairing

/-!
# T83: deterministic shift summation by parts

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module formalizes only the deterministic algebra in the unverified T82
note.  It concerns T69's residual-A12, `m = 1`, dyadic primitive-sector
sibling.  It proves no estimate at `Real.pi`, no T69 aggregate premise, no
full T29 predicate, and none of C1, C2, C3, or the canonical collision bound.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T83

open Theory.PiDigits.LongLagBlockCollisionDecay.T66
open Theory.PiDigits.LongLagBlockCollisionDecay.T68
open Theory.PiDigits.LongLagBlockCollisionDecay.T69
open Theory.PiDigits.LongLagBlockCollisionDecay.T76
open Theory.PiDigits.LongLagBlockCollisionDecay.T81

/-- A literal term of the T76 phase-variable version of T69's pooled sum. -/
def orbitTerm (α : ℝ) (h r k : ℕ) : ℂ :=
  Theory.PiDigits.T27.phase (pooledFrequency h r k : ℤ) α

/-- The multiplier-nine term created by the repunit recurrence. -/
def multiplierNine (α : ℝ) (h k : ℕ) : ℂ :=
  Theory.PiDigits.T27.phase ((9 * h * 10 ^ k : ℕ) : ℤ) α

/-- One frequency channel with an explicit orbit length. -/
def channelSum (α : ℝ) (h r L : ℕ) : ℂ :=
  ∑ k ∈ Finset.range L, orbitTerm α h r k

/-- Exact compression of the `h=1,10` equal-frequency class, including its
two singleton endpoints. -/
def pairedChannel (α : ℝ) (r L : ℕ) : ℂ :=
  orbitTerm α 1 r 0 +
    2 * (∑ k ∈ Finset.range (L - 1), orbitTerm α 1 r (k + 1)) +
      orbitTerm α 1 r L

/-- All ten channels after only the T76/T81 equal-frequency compression. -/
def compressedChannel (α : ℝ) (r L : ℕ) : ℂ :=
  pairedChannel α r L +
    ∑ h ∈ Finset.Icc 2 9, channelSum α h r L

theorem orbitTerm_adjacentFrequency (α : ℝ) (r k : ℕ) :
    orbitTerm α 10 r k = orbitTerm α 1 r (k + 1) := by
  unfold orbitTerm
  rw [adjacentFrequency_eq]

/-- The equal-frequency compression with the original inclusive `h` range
visible in the theorem type. -/
theorem equalFrequency_compression
    (α : ℝ) (r n : ℕ) :
    (∑ h ∈ Finset.Icc (1 : ℕ) 10, channelSum α h r (n + 1)) =
      orbitTerm α 1 r 0 +
        2 * (∑ k ∈ Finset.range n, orbitTerm α 1 r (k + 1)) +
          orbitTerm α 1 r (n + 1) +
            ∑ h ∈ Finset.Icc 2 9, channelSum α h r (n + 1) := by
  have hset : Finset.Icc (1 : ℕ) 10 =
      insert 1 (insert 10 (Finset.Icc 2 9)) := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset]
  have h1 : (1 : ℕ) ∉ insert 10 (Finset.Icc 2 9) := by simp
  have h10 : (10 : ℕ) ∉ Finset.Icc 2 9 := by simp
  rw [Finset.sum_insert h1, Finset.sum_insert h10]
  unfold channelSum
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp_rw [orbitTerm_adjacentFrequency]
  ring

/-- Literal T69 compression: `1<=h<=10`, `1<=r<H_t`, `k<N_t-r`, and the
triangular weight `H_t-r` all remain in the theorem type. -/
theorem literal_T69_equalFrequency_compression
    (t : ℕ) (α : ℝ) :
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
      ∑ r ∈ Finset.Ico 1 (H t),
        ((H t - r : ℕ) : ℂ) *
          (∑ k ∈ Finset.range (N t - r), orbitTerm α h r k)) =
      ∑ r ∈ Finset.Ico 1 (H t),
        ((H t - r : ℕ) : ℂ) * compressedChannel α r (N t - r) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.mul_sum]
  congr 1
  have hrH : r < H t := (Finset.mem_Ico.mp hr).2
  have hrN : r < N t := lt_of_lt_of_le hrH (H_le_N t)
  have hlen : N t - r = (N t - r - 1) + 1 := by omega
  rw [hlen]
  change (∑ h ∈ Finset.Icc (1 : ℕ) 10,
      channelSum α h r (N t - r - 1 + 1)) =
    compressedChannel α r (N t - r - 1 + 1)
  rw [equalFrequency_compression]
  simp only [compressedChannel, pairedChannel, Nat.add_sub_cancel]

/-- The exact natural-number recurrence behind the shift substitution. -/
theorem pooledFrequency_shift_recurrence (h r k : ℕ) :
    pooledFrequency h (r + 1) k =
      pooledFrequency h r (k + 1) + 9 * h * 10 ^ k := by
  have hp : 1 ≤ 10 ^ r := one_le_pow₀ (by omega)
  have hcore : 10 ^ r * 10 - 1 = 10 * (10 ^ r - 1) + 9 := by omega
  simp only [pooledFrequency, pow_succ]
  rw [hcore]
  ring

/-- Termwise recurrence substitution, with the multiplier-nine factor
displayed rather than hidden in a new frequency. -/
theorem orbitTerm_shift_recurrence (α : ℝ) (h r k : ℕ) :
    orbitTerm α h (r + 1) k =
      orbitTerm α h r (k + 1) * multiplierNine α h k := by
  unfold orbitTerm multiplierNine
  rw [← Theory.PiDigits.T27.phase_add]
  congr 1
  exact_mod_cast pooledFrequency_shift_recurrence h r k

/-- T81's unequal common cutoff, specialized to adjacent shifts while
retaining both original strict cutoffs and `max r (r+1)`. -/
theorem adjacent_unequalCutoff_iff
    {t r k : ℕ} (hr : r < H t) :
    (k < N t - r ∧ k < N t - (r + 1)) ↔
      k < N t - max r (r + 1) := by
  exact unequalCutoff_iff

/-- The signed difference for each unchanged channel `2<=h<=9`. -/
theorem channelSum_shift_difference
    (α : ℝ) (h r n : ℕ) :
    channelSum α h (r + 1) n - channelSum α h r (n + 1) =
      -orbitTerm α h r 0 +
        ∑ k ∈ Finset.range n,
          orbitTerm α h r (k + 1) * (multiplierNine α h k - 1) := by
  unfold channelSum
  rw [Finset.sum_range_succ']
  simp_rw [orbitTerm_shift_recurrence]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- The signed local boundary left after the `h=1,10` compression. -/
def boundaryBlock (α : ℝ) (r : ℕ) : ℂ :=
  -orbitTerm α 1 r 0 - orbitTerm α 1 r 1 -
    ∑ h ∈ Finset.Icc 2 9, orbitTerm α h r 0

/-- Every multiplier-nine term in one adjacent-shift block.  Here the old
length is `p+2`, the new length is `p+1`, and the common `k` cutoff is
`0<=k<p+1`. -/
def correlationBlock (α : ℝ) (r p : ℕ) : ℂ :=
  orbitTerm α 1 r 1 * (multiplierNine α 1 0 - 1) +
    2 * (∑ k ∈ Finset.range p,
      orbitTerm α 1 r (k + 2) * (multiplierNine α 1 (k + 1) - 1)) +
    orbitTerm α 1 r (p + 2) * (multiplierNine α 1 (p + 1) - 1) +
    ∑ h ∈ Finset.Icc 2 9,
      ∑ k ∈ Finset.range (p + 1),
        orbitTerm α h r (k + 1) * (multiplierNine α h k - 1)

/-- Literal audit of every recurrence term: the compressed pair has endpoint
multiplicities `1,2,1`, while the unchanged channels retain `2<=h<=9` and the
common `0<=k<p+1` cutoff. -/
theorem correlationBlock_literal (α : ℝ) (r p : ℕ) :
    correlationBlock α r p =
      orbitTerm α 1 r 1 * (multiplierNine α 1 0 - 1) +
        2 * (∑ k ∈ Finset.range p,
          orbitTerm α 1 r (k + 2) *
            (multiplierNine α 1 (k + 1) - 1)) +
        orbitTerm α 1 r (p + 2) *
          (multiplierNine α 1 (p + 1) - 1) +
        ∑ h ∈ Finset.Icc 2 9,
          ∑ k ∈ Finset.range (p + 1),
            orbitTerm α h r (k + 1) *
              (multiplierNine α h k - 1) := by
  rfl

theorem pairedChannel_shift_difference
    (α : ℝ) (r p : ℕ) :
    pairedChannel α (r + 1) (p + 1) - pairedChannel α r (p + 2) =
      -orbitTerm α 1 r 0 - orbitTerm α 1 r 1 +
        orbitTerm α 1 r 1 * (multiplierNine α 1 0 - 1) +
        2 * (∑ k ∈ Finset.range p,
          orbitTerm α 1 r (k + 2) * (multiplierNine α 1 (k + 1) - 1)) +
        orbitTerm α 1 r (p + 2) *
          (multiplierNine α 1 (p + 1) - 1) := by
  unfold pairedChannel
  simp only [Nat.add_sub_cancel]
  rw [show p + 2 - 1 = p + 1 by omega, Finset.sum_range_succ']
  simp_rw [orbitTerm_shift_recurrence]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Complete adjacent-shift recurrence after compression, with all signed
boundary terms and all ten original channels represented. -/
theorem compressedChannel_shift_difference
    (α : ℝ) (r p : ℕ) :
    compressedChannel α (r + 1) (p + 1) -
        compressedChannel α r (p + 2) =
      boundaryBlock α r + correlationBlock α r p := by
  unfold compressedChannel boundaryBlock correlationBlock
  have hsplit :
      (pairedChannel α (r + 1) (p + 1) +
          ∑ h ∈ Finset.Icc 2 9, channelSum α h (r + 1) (p + 1)) -
        (pairedChannel α r (p + 2) +
          ∑ h ∈ Finset.Icc 2 9, channelSum α h r (p + 2)) =
      (pairedChannel α (r + 1) (p + 1) - pairedChannel α r (p + 2)) +
        ((∑ h ∈ Finset.Icc 2 9, channelSum α h (r + 1) (p + 1)) -
          ∑ h ∈ Finset.Icc 2 9, channelSum α h r (p + 2)) := by ring
  rw [hsplit]
  have hpair := pairedChannel_shift_difference α r p
  have hchannels :
      (∑ h ∈ Finset.Icc 2 9, channelSum α h (r + 1) (p + 1)) -
          ∑ h ∈ Finset.Icc 2 9, channelSum α h r (p + 2) =
        ∑ h ∈ Finset.Icc 2 9,
          (-orbitTerm α h r 0 +
            ∑ k ∈ Finset.range (p + 1),
              orbitTerm α h r (k + 1) *
                (multiplierNine α h k - 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    exact channelSum_shift_difference α h r (p + 1)
  rw [hpair, hchannels, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- The complete T69 adjacent-shift identity.  Its type exposes the original
shift range, both unequal orbit lengths, and the exact common-cutoff parameter
`N_t-r-2`. -/
theorem literal_T69_compressed_shift_difference
    (t r : ℕ) (hr : r ∈ Finset.Ico 1 (H t - 1)) :
    compressedChannel Real.pi (r + 1) (N t - (r + 1)) -
        compressedChannel Real.pi r (N t - r) =
      boundaryBlock Real.pi r +
        correlationBlock Real.pi r (N t - r - 2) := by
  have hrH : r + 1 < H t := by
    have := (Finset.mem_Ico.mp hr).2
    have hH3 := three_le_H t
    omega
  have hrN : r + 1 < N t := lt_of_lt_of_le hrH (H_le_N t)
  have hnew : N t - (r + 1) = (N t - r - 2) + 1 := by omega
  have hold : N t - r = (N t - r - 2) + 2 := by omega
  rw [hnew, hold]
  exact compressedChannel_shift_difference Real.pi r (N t - r - 2)

/-- The triangular Abel coefficient. -/
def abelCoefficient (H r : ℕ) : ℂ :=
  ((H - r : ℕ) : ℂ) * ((H - r - 1 : ℕ) : ℂ) / 2

/-- The initial triangular coefficient. -/
def initialCoefficient (H : ℕ) : ℂ :=
  (H : ℂ) * ((H - 1 : ℕ) : ℂ) / 2

theorem sum_range_forward_difference (C : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (C (j + 2) - C (j + 1))) =
      C (n + 1) - C 1 := by
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Finset.sum_range_sub (fun j => C (j + 1)) n

/-- A weighted telescoping identity used in the proof of the triangular Abel
formula. -/
theorem prefix_sum_eq_weighted_differences (C : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, C (j + 1)) =
      (n : ℂ) * C 1 +
        ∑ j ∈ Finset.range (n - 1),
          ((n - j - 1 : ℕ) : ℂ) * (C (j + 2) - C (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp
      | succ p =>
          rw [Finset.sum_range_succ, ih]
          rw [show p + 1 + 1 - 1 = p + 1 by omega,
            Finset.sum_range_succ]
          have hsplit :
              (∑ j ∈ Finset.range p,
                  (((p + 1 + 1 - j - 1 : ℕ) : ℂ) *
                    (C (j + 2) - C (j + 1)))) =
                (∑ j ∈ Finset.range p,
                  (((p + 1 - j - 1 : ℕ) : ℂ) *
                    (C (j + 2) - C (j + 1)))) +
                  ∑ j ∈ Finset.range p, (C (j + 2) - C (j + 1)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            have hjp : j < p := Finset.mem_range.mp hj
            have hcoef : p + 1 + 1 - j - 1 =
                (p + 1 - j - 1) + 1 := by omega
            rw [hcoef]
            push_cast
            ring
          rw [hsplit, sum_range_forward_difference]
          have hlast : p + 1 + 1 - p - 1 = 1 := by omega
          rw [hlast]
          norm_num
          push_cast
          ring

theorem triangular_range_summation_by_parts (C : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((n - j : ℕ) : ℂ) * C (j + 1)) =
      ((n : ℂ) * ((n : ℂ) + 1) / 2) * C 1 +
        ∑ j ∈ Finset.range (n - 1),
          (((n - j : ℕ) : ℂ) * ((n - j - 1 : ℕ) : ℂ) / 2) *
            (C (j + 2) - C (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hleft :
          (∑ j ∈ Finset.range n,
              (((n + 1 - j : ℕ) : ℂ) * C (j + 1))) =
            (∑ j ∈ Finset.range n,
              (((n - j : ℕ) : ℂ) * C (j + 1))) +
              ∑ j ∈ Finset.range n, C (j + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        push_cast [Nat.cast_sub (by omega : j ≤ n + 1),
          Nat.cast_sub (by omega : j ≤ n)]
        ring
      rw [hleft]
      have hlastCoefficient : n + 1 - n = 1 := by omega
      rw [hlastCoefficient]
      norm_num
      rw [add_assoc, ← Finset.sum_range_succ]
      rw [ih, prefix_sum_eq_weighted_differences]
      cases n with
      | zero => simp
      | succ p =>
          rw [show p + 1 + 1 - 1 = p + 1 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ]
          have hright :
              (∑ j ∈ Finset.range p,
                ((((p + 1 + 1 - j : ℕ) : ℂ) *
                    ((p + 1 + 1 - j - 1 : ℕ) : ℂ) / 2) *
                      (C (j + 2) - C (j + 1)))) =
                (∑ j ∈ Finset.range p,
                  ((((p + 1 - j : ℕ) : ℂ) *
                      ((p + 1 - j - 1 : ℕ) : ℂ) / 2) *
                        (C (j + 2) - C (j + 1)))) +
                  ∑ j ∈ Finset.range p,
                    (((p + 1 - j : ℕ) : ℂ) *
                      (C (j + 2) - C (j + 1))) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            have hjp : j < p := Finset.mem_range.mp hj
            have hfirst : p + 1 + 1 - j = (p + 1 - j) + 1 := by omega
            rw [hfirst]
            simp only [Nat.add_sub_cancel]
            push_cast [Nat.cast_sub (by omega : 1 ≤ p + 1 - j)]
            ring
          rw [hright]
          simp only [Nat.add_sub_cancel]
          have hprefix :
              (∑ j ∈ Finset.range p,
                (((p + 1 + 1 - j - 1 : ℕ) : ℂ) *
                  (C (j + 2) - C (j + 1)))) =
                ∑ j ∈ Finset.range p,
                  (((p + 1 - j : ℕ) : ℂ) *
                    (C (j + 2) - C (j + 1))) := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 2
            omega
          rw [hprefix]
          have hprefixLast : p + 1 + 1 - p - 1 = 1 := by omega
          have htwo : p + 1 + 1 - p = 2 := by omega
          rw [hprefixLast, htwo]
          norm_num
          push_cast
          ring

/-- Finite shift summation by parts with the original triangular weight and
the exact coefficients `W` and `b_r`. -/
theorem triangular_shift_summation_by_parts
    (C : ℕ → ℂ) (H : ℕ) (hH : 1 ≤ H) :
    (∑ r ∈ Finset.Ico 1 H, ((H - r : ℕ) : ℂ) * C r) =
      initialCoefficient H * C 1 +
        ∑ r ∈ Finset.Ico 1 (H - 1),
          abelCoefficient H r * (C (r + 1) - C r) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simpa [initialCoefficient, abelCoefficient, Nat.add_sub_cancel,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mul_comm] using
      triangular_range_summation_by_parts C n

theorem orbitTerm_pi_eq_shiftedCharacter (h r k : ℕ) :
    orbitTerm Real.pi h r k = shiftedCharacter h r k := by
  unfold orbitTerm Theory.PiDigits.T27.phase pooledFrequency
    shiftedCharacter shiftedFrequency
  congr 1

/-- T69's outer constants and real-part convention, with the complete
`h/r/k` sum written using the recurrence-compatible `orbitTerm`. -/
theorem aggregateEnergy_eq_real_literal_pooled (t : ℕ) :
    aggregateEnergy t =
      10 * (H t : ℝ) * N t +
        2 * ((∑ h ∈ Finset.Icc (1 : ℕ) 10,
          ∑ r ∈ Finset.Ico 1 (H t),
            ((H t - r : ℕ) : ℂ) *
              (∑ k ∈ Finset.range (N t - r),
                orbitTerm Real.pi h r k))).re := by
  rw [aggregateEnergy_eq_real_aggregateShiftedSum]
  congr 2

/-- The complete deterministic T69 identity.  The left side displays all ten
frequencies, strict shifts, unequal orbit cutoffs, and triangular weights.  On
the right, `initialCoefficient H = H*(H-1)/2`,
`abelCoefficient H r = (H-r)*(H-r-1)/2`, every signed local boundary is
literal, and `correlationBlock` is the recurrence-expanded multiplier-nine
sum from `compressedChannel_shift_difference`. -/
theorem literal_T69_shift_summation_by_parts (t : ℕ) :
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
      ∑ r ∈ Finset.Ico 1 (H t),
        ((H t - r : ℕ) : ℂ) *
          (∑ k ∈ Finset.range (N t - r),
            orbitTerm Real.pi h r k)) =
      (((H t : ℕ) : ℂ) * ((H t - 1 : ℕ) : ℂ) / 2) *
          compressedChannel Real.pi 1 (N t - 1) +
        (∑ r ∈ Finset.Ico 1 (H t - 1),
          (((H t - r : ℕ) : ℂ) * ((H t - r - 1 : ℕ) : ℂ) / 2) *
            (-orbitTerm Real.pi 1 r 0 - orbitTerm Real.pi 1 r 1 -
              ∑ h ∈ Finset.Icc 2 9, orbitTerm Real.pi h r 0)) +
        ∑ r ∈ Finset.Ico 1 (H t - 1),
          (((H t - r : ℕ) : ℂ) * ((H t - r - 1 : ℕ) : ℂ) / 2) *
            correlationBlock Real.pi r (N t - r - 2) := by
  rw [literal_T69_equalFrequency_compression]
  rw [triangular_shift_summation_by_parts
    (fun r => compressedChannel Real.pi r (N t - r)) (H t)
    (by exact_mod_cast H_pos t)]
  simp only [initialCoefficient, abelCoefficient]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [literal_T69_compressed_shift_difference t r hr]
  unfold boundaryBlock
  ring

/-- The separated two-shift coefficient mass before evaluating any phase. -/
def separatedMass (N H : ℕ) : ℝ :=
  10 * ∑ r ∈ Finset.Ico 1 (H - 1),
    ((H - r : ℕ) : ℝ) * ((H - r - 1 : ℕ) : ℝ) *
      ((N - r - 1 : ℕ) : ℝ)

theorem sum_range_cube_real (n : ℕ) :
    (∑ r ∈ Finset.range n, (r : ℝ) ^ 3) =
      ((n : ℝ) * ((n : ℝ) - 1) / 2) ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Exact even-scale polynomial, including the constant `5/6`. -/
theorem separatedMass_evenScale_formula (q : ℕ) (hq : 2 ≤ q) :
    separatedMass (q ^ 2 + 1) (q + 1) =
      (5 / 6 : ℝ) * q * (q - 1) * (q + 1) * (4 * q ^ 2 - q - 2) := by
  have hq1 : 1 ≤ q := by omega
  have hterm (r : ℕ) (hr : r ∈ Finset.Ico 1 q) :
      (((q + 1 - r : ℕ) : ℝ) * ((q + 1 - r - 1 : ℕ) : ℝ) *
          ((q ^ 2 + 1 - r - 1 : ℕ) : ℝ)) =
        (((q : ℝ) + 1 - r) * ((q : ℝ) - r) * ((q : ℝ) ^ 2 - r)) := by
    have hrq : r < q := (Finset.mem_Ico.mp hr).2
    have hrq1 : r ≤ q + 1 := by omega
    have hrq2 : r ≤ q ^ 2 := by nlinarith
    have hfirst : q + 1 - r - 1 = q - r := by omega
    have hsecond : q ^ 2 + 1 - r - 1 = q ^ 2 - r := by omega
    rw [hfirst, hsecond, Nat.cast_sub hrq1,
      Nat.cast_sub (Nat.le_of_lt hrq), Nat.cast_sub hrq2]
    push_cast
    ring
  unfold separatedMass
  simp only [Nat.add_sub_cancel]
  calc
    10 * ∑ r ∈ Finset.Ico 1 q,
        ((q + 1 - r : ℕ) : ℝ) * ((q + 1 - r - 1 : ℕ) : ℝ) *
          ((q ^ 2 + 1 - r - 1 : ℕ) : ℝ) =
        10 * ∑ r ∈ Finset.Ico 1 q,
          (((q : ℝ) + 1 - r) * ((q : ℝ) - r) *
            ((q : ℝ) ^ 2 - r)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro r hr
              exact hterm r hr
    _ = 10 * ((∑ r ∈ Finset.range q,
          (((q : ℝ) + 1 - r) * ((q : ℝ) - r) *
            ((q : ℝ) ^ 2 - r))) -
          (((q : ℝ) + 1) * (q : ℝ) * (q : ℝ) ^ 2)) := by
            rw [Finset.sum_Ico_eq_sub _ hq1]
            norm_num
    _ = (5 / 6 : ℝ) * q * (q - 1) * (q + 1) *
          (4 * q ^ 2 - q - 2) := by
      simp_rw [show ∀ r : ℕ,
          (((q : ℝ) + 1 - r) * ((q : ℝ) - r) * ((q : ℝ) ^ 2 - r)) =
            ((q : ℝ) ^ 4 + (q : ℝ) ^ 3) +
              (-((2 * (q : ℝ) ^ 3 + 2 * (q : ℝ) ^ 2 + q) * r)) +
                ((q : ℝ) ^ 2 + 2 * q + 1) * (r : ℝ) ^ 2 +
                  (-((r : ℝ) ^ 3)) by
        intro r
        push_cast
        ring]
      simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp_rw [Finset.sum_const]
      rw [← Finset.mul_sum, ← Finset.mul_sum,
        Theory.PiDigits.LongLagBlockCollisionDecay.T69.sum_range_id_real,
        Theory.PiDigits.LongLagBlockCollisionDecay.T69.sum_range_sq_real,
        sum_range_cube_real]
      simp only [Finset.card_range, nsmul_eq_mul]
      push_cast [Nat.cast_sub hq1]
      ring

/-- The same polynomial identity with the original shift range and every
factor from the doubled Abel coefficient and common orbit length exposed. -/
theorem separatedMass_evenScale_polynomial_literal (q : ℕ) (hq : 2 ≤ q) :
    10 * ∑ r ∈ Finset.Ico 1 ((q + 1) - 1),
      (((q + 1) - r : ℕ) : ℝ) *
        (((q + 1) - r - 1 : ℕ) : ℝ) *
          (((q ^ 2 + 1) - r - 1 : ℕ) : ℝ) =
      (5 / 6 : ℝ) * q * (q - 1) * (q + 1) *
        (4 * q ^ 2 - q - 2) := by
  simpa only [separatedMass] using separatedMass_evenScale_formula q hq

/-- Explicit target-normalized lower bound on every even scale. -/
theorem separatedMass_normalized_lower (q : ℕ) (hq : 2 ≤ q) :
    (5 / 6 : ℝ) * q ^ 2 ≤
      separatedMass (q ^ 2 + 1) (q + 1) /
        (((q + 1 : ℕ) : ℝ) * ((q ^ 2 + 1 : ℕ) : ℝ)) := by
  rw [separatedMass_evenScale_formula q hq]
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpoly : (2 : ℝ) * ((q : ℝ) ^ 2 + 1) ≤
      4 * (q : ℝ) ^ 2 - q - 2 := by nlinarith
  have hquad : (q : ℝ) ^ 2 ≤ 2 * q * (q - 1) := by nlinarith
  have hden : (0 : ℝ) <
      (((q + 1 : ℕ) : ℝ) * ((q ^ 2 + 1 : ℕ) : ℝ)) := by positivity
  apply (le_div_iff₀ hden).2
  push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
  calc
    (5 / 6 : ℝ) * (q : ℝ) ^ 2 *
        (((q : ℝ) + 1) * ((q : ℝ) ^ 2 + 1)) ≤
      (5 / 6 : ℝ) * (2 * q * (q - 1)) *
        (((q : ℝ) + 1) * ((q : ℝ) ^ 2 + 1)) := by gcongr
    _ = (5 / 6 : ℝ) * q * (q - 1) * ((q : ℝ) + 1) *
        (2 * ((q : ℝ) ^ 2 + 1)) := by ring
    _ ≤ (5 / 6 : ℝ) * q * (q - 1) * ((q : ℝ) + 1) *
        (4 * (q : ℝ) ^ 2 - q - 2) := by
          have hqm1 : (0 : ℝ) ≤ q - 1 := by linarith
          have hcoef : (0 : ℝ) ≤
              (5 / 6 : ℝ) * q * (q - 1) * ((q : ℝ) + 1) := by positivity
          exact mul_le_mul_of_nonneg_left hpoly hcoef

/-- Literal normalized lower bound: the exact separated mass sum, its
`1<=r<=q-1` range, polynomial factors, target denominator, and `5/6` constant
all occur in the theorem type. -/
theorem separatedMass_normalized_lower_literal (q : ℕ) (hq : 2 ≤ q) :
    (5 / 6 : ℝ) * q ^ 2 ≤
      (10 * ∑ r ∈ Finset.Ico 1 ((q + 1) - 1),
        (((q + 1) - r : ℕ) : ℝ) *
          (((q + 1) - r - 1 : ℕ) : ℝ) *
            (((q ^ 2 + 1) - r - 1 : ℕ) : ℝ)) /
        (((q + 1 : ℕ) : ℝ) * ((q ^ 2 + 1 : ℕ) : ℝ)) := by
  simpa only [separatedMass] using separatedMass_normalized_lower q hq

/-- The exact T81 even-scale family has separated mass exceeding every
constant multiple of T69's `H_t*N_t` target. -/
theorem exists_evenScale_separatedMass_exceeds (C : ℝ) :
    ∃ m : ℕ,
      C * ((H (2 * m) : ℝ) * N (2 * m)) <
        separatedMass (N (2 * m)) (H (2 * m)) := by
  obtain ⟨m, hm⟩ :=
    pow_unbounded_of_one_lt ((6 / 5 : ℝ) * C + 1)
      (by norm_num : (1 : ℝ) < 2)
  let q := evenScaleBase m
  have hq : 2 ≤ q := evenScaleBase_two_le m
  have hmono : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) := by
    rw [pow_succ]
    have hp : (0 : ℝ) ≤ 2 ^ m := by positivity
    nlinarith
  have hbase : (6 / 5 : ℝ) * C + 1 < (q : ℝ) := by
    change (6 / 5 : ℝ) * C + 1 < (evenScaleBase m : ℝ)
    rw [show (evenScaleBase m : ℝ) = (2 : ℝ) ^ (m + 1) by
      simp [evenScaleBase]]
    exact hm.trans_le hmono
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have htarget : C < (5 / 6 : ℝ) * (q : ℝ) ^ 2 := by
    have hqq : (q : ℝ) ≤ q ^ 2 := by nlinarith
    nlinarith
  have hlower := separatedMass_normalized_lower q hq
  have hratio : C <
      separatedMass (q ^ 2 + 1) (q + 1) /
        (((q + 1 : ℕ) : ℝ) * ((q ^ 2 + 1 : ℕ) : ℝ)) :=
    htarget.trans_le hlower
  have hpositive : (0 : ℝ) <
      (((q + 1 : ℕ) : ℝ) * ((q ^ 2 + 1 : ℕ) : ℝ)) := by positivity
  refine ⟨m, ?_⟩
  rw [H_evenScale, N_evenScale]
  exact (lt_div_iff₀ hpositive).mp hratio

end Theory.PiDigits.LongLagBlockCollisionDecay.T83

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.equalFrequency_compression
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.literal_T69_equalFrequency_compression
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.pooledFrequency_shift_recurrence
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.orbitTerm_shift_recurrence
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.adjacent_unequalCutoff_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.channelSum_shift_difference
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.pairedChannel_shift_difference
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.correlationBlock_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.compressedChannel_shift_difference
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.literal_T69_compressed_shift_difference
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.triangular_shift_summation_by_parts
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.aggregateEnergy_eq_real_literal_pooled
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.literal_T69_shift_summation_by_parts
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.separatedMass_evenScale_formula
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.separatedMass_evenScale_polynomial_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.separatedMass_normalized_lower
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.separatedMass_normalized_lower_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T83.exists_evenScale_separatedMass_exceeds
