import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Denominator exponents absorb logarithmic powers

Exponent addition is normalized before division, with every real power
nonzero because its base is positive.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A sufficiently large denominator exponent absorbs a multiplicative real power. -/
theorem rpow_mul_div_le_div {L X u v w : Real}
    (hL : 1 <= L) (hX : 0 <= X) (hDegree : u + w <= v) :
    L ^ u * (X / L ^ v) <= X / L ^ w := by
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hVPos : 0 < L ^ v := Real.rpow_pos_of_pos hLPos v
  have hWPos : 0 < L ^ w := Real.rpow_pos_of_pos hLPos w
  have hVNe : Ne (L ^ v) 0 := ne_of_gt hVPos
  have hWNe : Ne (L ^ w) 0 := ne_of_gt hWPos
  have hProduct : (L ^ u * (X / L ^ v)) * L ^ w <= X := by
    calc
      (L ^ u * (X / L ^ v)) * L ^ w = X * L ^ (u + w) / L ^ v := by
        rw [Real.rpow_add hLPos u w]
        ring
      _ <= X * L ^ v / L ^ v :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hDegree) hX)
          hVPos.le
      _ = X := by field_simp
  calc
    L ^ u * (X / L ^ v) = (L ^ u * (X / L ^ v)) * L ^ w / L ^ w := by field_simp
    _ <= X / L ^ w := div_le_div_of_nonneg_right hProduct hWPos.le

/-- Natural numerator powers use the same denominator-exponent normalization. -/
theorem pow_mul_div_le_div {L X v w : Real} (n : Nat)
    (hL : 1 <= L) (hX : 0 <= X) (hDegree : (n : Real) + w <= v) :
    L ^ n * (X / L ^ v) <= X / L ^ w := by
  simpa only [Real.rpow_natCast] using
    (rpow_mul_div_le_div (L := L) (X := X) (u := (n : Real)) (v := v) (w := w)
      hL hX hDegree)

end BombieriVinogradov.RealAnalysis
