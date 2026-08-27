import TheoryLib.PiQuantitativeBlockHitting.T180T180ReflectedTrigIntervalCore

/-!
# T181: reflected common-scale interval arithmetic

This file supplies the small semantic layer between the T180 trigonometric
leaves and a generated reflected score certificate.  Every interval uses the
same positive natural scale and stores only integer endpoints.  The executable
checks contain no rational or real arithmetic: a generated output row is
accepted only when integer endpoint inequalities prove it is an outward
rounding of the requested operation.

Multiplication checks all four endpoint products.  Squaring has a separate
checker so that an interval crossing zero receives the sharp lower bound
zero.  Division never executes rational division: after checking that the
denominator interval is positive, it cross-multiplies both denominator
endpoints.  The theorems below give the corresponding real semantics.
-/

namespace Theory.PiDigits.T181ReflectedIntervalArithmetic

open Theory.PiDigits.T171CompactFixedPointCertificate

/-- Real semantics of an integer interval at a common scale. -/
def EnclosesReal (scale : Nat) (row : FixedInterval) (x : Real) : Prop :=
  (row.lower : Real) ≤ (scale : Real) * x ∧
    (scale : Real) * x ≤ (row.upper : Real)

/-- Exact common-scale addition row. -/
def addInterval (a b : FixedInterval) : FixedInterval :=
  ⟨a.lower + b.lower, a.upper + b.upper⟩

/-- Exact common-scale subtraction row. -/
def subInterval (a b : FixedInterval) : FixedInterval :=
  ⟨a.lower - b.upper, a.upper - b.lower⟩

/-- The generated output encloses the exact addition row. -/
def checkAdd (a b out : FixedInterval) : Bool :=
  decide (out.lower ≤ a.lower + b.lower ∧
    a.upper + b.upper ≤ out.upper)

/-- The generated output encloses the exact subtraction row. -/
def checkSub (a b out : FixedInterval) : Bool :=
  decide (out.lower ≤ a.lower - b.upper ∧
    a.upper - b.lower ≤ out.upper)

/-- Four-corner outward multiplication check.  Multiplication raises the
input scale to its square, so the proposed common-scale output is multiplied
by `scale` in these integer comparisons. -/
def checkMul (scale : Nat) (a b out : FixedInterval) : Bool :=
  decide (
    out.lower * scale ≤ a.lower * b.lower ∧
    out.lower * scale ≤ a.lower * b.upper ∧
    out.lower * scale ≤ a.upper * b.lower ∧
    out.lower * scale ≤ a.upper * b.upper ∧
    a.lower * b.lower ≤ out.upper * scale ∧
    a.lower * b.upper ≤ out.upper * scale ∧
    a.upper * b.lower ≤ out.upper * scale ∧
    a.upper * b.upper ≤ out.upper * scale)

/-- Dedicated square check.  When the input crosses zero the lower endpoint
is checked against zero; otherwise both endpoint squares are checked. -/
def checkSquare (scale : Nat) (a out : FixedInterval) : Bool :=
  decide (
    (if a.lower ≤ 0 ∧ 0 ≤ a.upper then out.lower ≤ 0
      else out.lower * scale ≤ a.lower * a.lower ∧
        out.lower * scale ≤ a.upper * a.upper) ∧
    a.lower * a.lower ≤ out.upper * scale ∧
    a.upper * a.upper ≤ out.upper * scale)

/-- Positive-denominator division check by cross multiplication.  Both
denominator endpoints are checked because the sign of an output endpoint is
not trusted. -/
def checkDiv (scale : Nat) (num den out : FixedInterval) : Bool :=
  decide (
    0 < den.lower ∧
    out.lower * den.lower ≤ scale * num.lower ∧
    out.lower * den.upper ≤ scale * num.lower ∧
    scale * num.upper ≤ out.upper * den.lower ∧
    scale * num.upper ≤ out.upper * den.upper)

private theorem four_corners_lower
    {a x b c y d : Real} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d)
    {L : Real} (hac : L ≤ a * c) (had : L ≤ a * d)
    (hbc : L ≤ b * c) (hbd : L ≤ b * d) :
    L ≤ x * y := by
  by_cases hx0 : 0 ≤ x
  · have hxy : x * c ≤ x * y := mul_le_mul_of_nonneg_left hy.1 hx0
    by_cases hc0 : 0 ≤ c
    · exact hac.trans ((mul_le_mul_of_nonneg_right hx.1 hc0).trans hxy)
    · have hc : c ≤ 0 := le_of_not_ge hc0
      exact hbc.trans ((mul_le_mul_of_nonpos_right hx.2 hc).trans hxy)
  · have hxneg : x ≤ 0 := le_of_not_ge hx0
    have hxy : x * d ≤ x * y := mul_le_mul_of_nonpos_left hy.2 hxneg
    by_cases hd0 : 0 ≤ d
    · exact had.trans ((mul_le_mul_of_nonneg_right hx.1 hd0).trans hxy)
    · have hd : d ≤ 0 := le_of_not_ge hd0
      exact hbd.trans ((mul_le_mul_of_nonpos_right hx.2 hd).trans hxy)

private theorem four_corners_upper
    {a x b c y d : Real} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d)
    {U : Real} (hac : a * c ≤ U) (had : a * d ≤ U)
    (hbc : b * c ≤ U) (hbd : b * d ≤ U) :
    x * y ≤ U := by
  by_cases hx0 : 0 ≤ x
  · have hxy : x * y ≤ x * d := mul_le_mul_of_nonneg_left hy.2 hx0
    by_cases hd0 : 0 ≤ d
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hd0).trans hbd)
    · have hd : d ≤ 0 := le_of_not_ge hd0
      exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 hd).trans had)
  · have hxneg : x ≤ 0 := le_of_not_ge hx0
    have hxy : x * y ≤ x * c := mul_le_mul_of_nonpos_left hy.1 hxneg
    by_cases hc0 : 0 ≤ c
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hc0).trans hbc)
    · have hc : c ≤ 0 := le_of_not_ge hc0
      exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 hc).trans hac)

theorem checkAdd_sound {scale : Nat} {a b out : FixedInterval} {x y : Real}
    (ha : EnclosesReal scale a x) (hb : EnclosesReal scale b y)
    (hc : checkAdd a b out = true) :
    EnclosesReal scale out (x + y) := by
  have hc' := of_decide_eq_true hc
  unfold EnclosesReal at ha hb ⊢
  have hcR : (out.lower : Real) ≤ a.lower + b.lower ∧
      (a.upper : Real) + b.upper ≤ out.upper := by exact_mod_cast hc'
  constructor
  · calc
      (out.lower : Real) ≤ a.lower + b.lower := hcR.1
      _ ≤ scale * x + scale * y := add_le_add ha.1 hb.1
      _ = scale * (x + y) := by ring
  · calc
      (scale : Real) * (x + y) = scale * x + scale * y := by ring
      _ ≤ a.upper + b.upper := add_le_add ha.2 hb.2
      _ ≤ out.upper := hcR.2

theorem checkSub_sound {scale : Nat} {a b out : FixedInterval} {x y : Real}
    (ha : EnclosesReal scale a x) (hb : EnclosesReal scale b y)
    (hc : checkSub a b out = true) :
    EnclosesReal scale out (x - y) := by
  have hc' := of_decide_eq_true hc
  unfold EnclosesReal at ha hb ⊢
  have hcR : (out.lower : Real) ≤ a.lower - b.upper ∧
      (a.upper : Real) - b.lower ≤ out.upper := by exact_mod_cast hc'
  constructor
  · calc
      (out.lower : Real) ≤ a.lower - b.upper := hcR.1
      _ ≤ scale * x - scale * y := sub_le_sub ha.1 hb.2
      _ = scale * (x - y) := by ring
  · calc
      (scale : Real) * (x - y) = scale * x - scale * y := by ring
      _ ≤ a.upper - b.lower := sub_le_sub ha.2 hb.1
      _ ≤ out.upper := hcR.2

theorem checkMul_sound {scale : Nat} {a b out : FixedInterval} {x y : Real}
    (hscale : 0 < scale) (ha : EnclosesReal scale a x)
    (hb : EnclosesReal scale b y) (hc : checkMul scale a b out = true) :
    EnclosesReal scale out (x * y) := by
  have hc' := of_decide_eq_true hc
  unfold EnclosesReal at ha hb ⊢
  rcases hc' with ⟨hll, hlu, hul, huu, ull, ulu, uul, uuu⟩
  have hllR : (out.lower : Real) * scale ≤ a.lower * b.lower := by exact_mod_cast hll
  have hluR : (out.lower : Real) * scale ≤ a.lower * b.upper := by exact_mod_cast hlu
  have hulR : (out.lower : Real) * scale ≤ a.upper * b.lower := by exact_mod_cast hul
  have huuR : (out.lower : Real) * scale ≤ a.upper * b.upper := by exact_mod_cast huu
  have ullR : (a.lower : Real) * b.lower ≤ out.upper * scale := by exact_mod_cast ull
  have uluR : (a.lower : Real) * b.upper ≤ out.upper * scale := by exact_mod_cast ulu
  have uulR : (a.upper : Real) * b.lower ≤ out.upper * scale := by exact_mod_cast uul
  have uuuR : (a.upper : Real) * b.upper ≤ out.upper * scale := by exact_mod_cast uuu
  have hs : (0 : Real) < scale := by exact_mod_cast hscale
  let X : Real := scale * x
  let Y : Real := scale * y
  have hXY : X * Y = (scale : Real) ^ 2 * (x * y) := by
    dsimp [X, Y]
    ring
  have hl : (out.lower : Real) * scale ≤ X * Y := by
    apply four_corners_lower ha hb
    · exact hllR
    · exact hluR
    · exact hulR
    · exact huuR
  have hu : X * Y ≤ (out.upper : Real) * scale := by
    apply four_corners_upper ha hb
    · exact ullR
    · exact uluR
    · exact uulR
    · exact uuuR
  rw [hXY] at hl hu
  constructor <;> nlinarith [sq_pos_of_pos hs]

theorem checkSquare_sound {scale : Nat} {a out : FixedInterval} {x : Real}
    (hscale : 0 < scale) (ha : EnclosesReal scale a x)
    (hc : checkSquare scale a out = true) :
    EnclosesReal scale out (x ^ 2) := by
  have hc' := of_decide_eq_true hc
  unfold EnclosesReal at ha ⊢
  have hs : (0 : Real) < scale := by exact_mod_cast hscale
  let X : Real := scale * x
  have hXsq : X ^ 2 = (scale : Real) ^ 2 * x ^ 2 := by
    dsimp [X]
    ring
  have hl : (out.lower : Real) * scale ≤ X ^ 2 := by
    by_cases hcross : (a.lower : Real) ≤ 0 ∧ 0 ≤ (a.upper : Real)
    · have hbranch : (out.lower : Real) ≤ 0 := by
        have hcrossI : a.lower ≤ 0 ∧ 0 ≤ a.upper := by exact_mod_cast hcross
        have := hc'.1
        simp only [if_pos hcrossI] at this
        exact_mod_cast this
      have hscaled : (out.lower : Real) * scale ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hbranch hs.le
      exact hscaled.trans (sq_nonneg X)
    · have hcrossI : ¬(a.lower ≤ 0 ∧ 0 ≤ a.upper) := by exact_mod_cast hcross
      have hraw := hc'.1
      simp only [if_neg hcrossI] at hraw
      have hends : (out.lower : Real) * scale ≤
          (a.lower : Real) ^ 2 ∧
          (out.lower : Real) * scale ≤ (a.upper : Real) ^ 2 := by
        constructor
        · simpa [pow_two] using (show (out.lower : Real) * scale ≤
            (a.lower : Real) * a.lower by exact_mod_cast hraw.1)
        · simpa [pow_two] using (show (out.lower : Real) * scale ≤
            (a.upper : Real) * a.upper by exact_mod_cast hraw.2)
      rcases not_and_or.mp hcross with hleft | hright
      · have hleft' : 0 ≤ (a.lower : Real) := le_of_not_ge hleft
        have hX0 : 0 ≤ X := ha.1.trans' hleft'
        exact hends.1.trans ((sq_le_sq₀ hleft' hX0).2 ha.1)
      · have hright' : (a.upper : Real) ≤ 0 := le_of_not_ge hright
        have hnegX : 0 ≤ -X := by linarith
        have hnegU : 0 ≤ -(a.upper : Real) := by linarith
        have hsquares : (a.upper : Real) ^ 2 ≤ X ^ 2 := by
          have := (sq_le_sq₀ hnegU hnegX).2 (by linarith [ha.2] : -a.upper ≤ -X)
          simpa using this
        exact hends.2.trans hsquares
  have hu : X ^ 2 ≤ (out.upper : Real) * scale := by
    have hlowSq : (a.lower : Real) ^ 2 ≤ (out.upper : Real) * scale := by
      simpa [pow_two] using (show (a.lower : Real) * a.lower ≤
        (out.upper : Real) * scale by exact_mod_cast hc'.2.1)
    have huppSq : (a.upper : Real) ^ 2 ≤ (out.upper : Real) * scale := by
      simpa [pow_two] using (show (a.upper : Real) * a.upper ≤
        (out.upper : Real) * scale by exact_mod_cast hc'.2.2)
    by_cases hX : 0 ≤ X
    · by_cases hu0 : 0 ≤ (a.upper : Real)
      · exact (sq_le_sq₀ hX hu0).2 ha.2 |>.trans huppSq
      · nlinarith
    · have hX' : X ≤ 0 := le_of_not_ge hX
      by_cases hl0 : (a.lower : Real) ≤ 0
      · have hsquares : X ^ 2 ≤ (a.lower : Real) ^ 2 := by
          nlinarith [sq_nonneg (X - (a.lower : Real))]
        exact hsquares.trans hlowSq
      · nlinarith
  rw [hXsq] at hl hu
  constructor <;> nlinarith [sq_pos_of_pos hs]

theorem checkDiv_sound {scale : Nat} {num den out : FixedInterval}
    {x y : Real} (hscale : 0 < scale) (hnum : EnclosesReal scale num x)
    (hden : EnclosesReal scale den y) (hc : checkDiv scale num den out = true) :
    EnclosesReal scale out (x / y) := by
  have hc' := of_decide_eq_true hc
  unfold EnclosesReal at hnum hden ⊢
  rcases hc' with ⟨hdenPos, hll, hlu, hul, huu⟩
  have hllR : (out.lower : Real) * den.lower ≤ scale * num.lower := by exact_mod_cast hll
  have hluR : (out.lower : Real) * den.upper ≤ scale * num.lower := by exact_mod_cast hlu
  have hulR : (scale : Real) * num.upper ≤ out.upper * den.lower := by exact_mod_cast hul
  have huuR : (scale : Real) * num.upper ≤ out.upper * den.upper := by exact_mod_cast huu
  have hs : (0 : Real) < scale := by exact_mod_cast hscale
  have hdenLower : (0 : Real) < den.lower := by exact_mod_cast hdenPos
  have hsy : (0 : Real) < scale * y := hdenLower.trans_le hden.1
  have hy : 0 < y := pos_of_mul_pos_right hsy hs.le
  have hlY : (out.lower : Real) * (scale * y) ≤
      (scale : Real) * (scale * x) := by
    by_cases hout : 0 ≤ (out.lower : Real)
    · calc
        (out.lower : Real) * (scale * y) ≤ out.lower * den.upper :=
          mul_le_mul_of_nonneg_left hden.2 hout
        _ ≤ scale * num.lower := hluR
        _ ≤ scale * (scale * x) := mul_le_mul_of_nonneg_left hnum.1 hs.le
    · have hout' : (out.lower : Real) ≤ 0 := le_of_not_ge hout
      calc
        (out.lower : Real) * (scale * y) ≤ out.lower * den.lower :=
          mul_le_mul_of_nonpos_left hden.1 hout'
        _ ≤ scale * num.lower := hllR
        _ ≤ scale * (scale * x) := mul_le_mul_of_nonneg_left hnum.1 hs.le
  have huY : (scale : Real) * (scale * x) ≤
      (out.upper : Real) * (scale * y) := by
    calc
      (scale : Real) * (scale * x) ≤ scale * num.upper :=
        mul_le_mul_of_nonneg_left hnum.2 hs.le
      _ ≤ (out.upper : Real) * (scale * y) := by
        by_cases hout : 0 ≤ (out.upper : Real)
        · exact hulR.trans (mul_le_mul_of_nonneg_left hden.1 hout)
        · have hout' : (out.upper : Real) ≤ 0 := le_of_not_ge hout
          exact huuR.trans (mul_le_mul_of_nonpos_left hden.2 hout')
  have hl : (out.lower : Real) * y ≤ scale * x := by
    apply (mul_le_mul_iff_left₀ hs).mp
    convert hlY using 1 <;> ring
  have hu : (scale : Real) * x ≤ out.upper * y := by
    apply (mul_le_mul_iff_left₀ hs).mp
    convert huY using 1 <;> ring
  constructor
  · rw [show (scale : Real) * (x / y) = (scale * x) / y by ring]
    exact (le_div_iff₀ hy).2 hl
  · rw [show (scale : Real) * (x / y) = (scale * x) / y by ring]
    exact (div_le_iff₀ hy).2 hu

/-! Small executable examples exercise negative products, a zero-crossing
square, and a positive division interval at scale ten. -/

private def aDemo : FixedInterval := ⟨-12, -8⟩
private def bDemo : FixedInterval := ⟨3, 7⟩

example : checkAdd aDemo bDemo ⟨-9, -1⟩ = true := by rfl
example : checkSub aDemo bDemo ⟨-19, -11⟩ = true := by rfl
example : checkMul 10 aDemo bDemo ⟨-9, -2⟩ = true := by rfl
example : checkSquare 10 ⟨-3, 4⟩ ⟨0, 2⟩ = true := by rfl
example : checkDiv 10 ⟨-12, -8⟩ ⟨3, 7⟩ ⟨-40, -11⟩ = true := by rfl

end Theory.PiDigits.T181ReflectedIntervalArithmetic

#print axioms Theory.PiDigits.T181ReflectedIntervalArithmetic.checkAdd_sound
#print axioms Theory.PiDigits.T181ReflectedIntervalArithmetic.checkSub_sound
#print axioms Theory.PiDigits.T181ReflectedIntervalArithmetic.checkMul_sound
#print axioms Theory.PiDigits.T181ReflectedIntervalArithmetic.checkSquare_sound
#print axioms Theory.PiDigits.T181ReflectedIntervalArithmetic.checkDiv_sound
