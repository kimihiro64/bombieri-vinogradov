import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Transferring a normalized decay factor to a denominator

A cutoff bounded by a real power retains the normalization supplied by a
nonnegative decay factor. The numerator itself may vanish.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Convert a power-normalized decay bound into the required denominator scale. -/
theorem cutoff_mul_mul_le_div_of_decay {L X E r B w : Real}
    (hL : 0 < L) (hX : 0 <= X) (hE : 0 <= E) (hR : r <= L ^ B)
    (hDecay : L ^ (B + w) * E <= 1) :
    r * X * E <= X / L ^ w := by
  have hWPos : 0 < L ^ w := Real.rpow_pos_of_pos hL w
  have hWNe : Ne (L ^ w) 0 := ne_of_gt hWPos
  have hScalar : r * L ^ w * E <= 1 := by
    calc
      r * L ^ w * E <= L ^ B * L ^ w * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR hWPos.le) hE
      _ = L ^ (B + w) * E := by rw [Real.rpow_add hL B w]
      _ <= 1 := hDecay
  have hProduct : (r * X * E) * L ^ w <= X := by
    calc
      (r * X * E) * L ^ w = X * (r * L ^ w * E) := by ring
      _ <= X * 1 := mul_le_mul_of_nonneg_left hScalar hX
      _ = X := by ring
  calc
    r * X * E = (r * X * E) * L ^ w / L ^ w := by field_simp
    _ <= X / L ^ w := div_le_div_of_nonneg_right hProduct hWPos.le

end BombieriVinogradov.RealAnalysis
