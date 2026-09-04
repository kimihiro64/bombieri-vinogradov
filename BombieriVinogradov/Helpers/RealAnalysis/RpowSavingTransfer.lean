import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Transferring a power saving to a logarithmic denominator

The degree and power-gap comparisons are explicit hypotheses. No positive
gap is needed for this conditional algebraic step itself.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A cumulative power saving absorbs the numerator logarithmic degree. -/
theorem rpow_mul_rpow_le_div_of_saving {X L b t delta w p : Real}
    (hX : 1 <= X) (hL : 1 <= L) (hLog : L ^ b <= X ^ delta)
    (hDegree : w + p <= b) (hGap : t + delta <= 1) :
    X ^ t * L ^ p <= X / L ^ w := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hWPos : 0 < L ^ w := Real.rpow_pos_of_pos hLPos w
  have hWNe : Ne (L ^ w) 0 := ne_of_gt hWPos
  have hLogDegree : L ^ (w + p) <= X ^ delta :=
    (Real.rpow_le_rpow_of_exponent_le hL hDegree).trans hLog
  have hProduct : (X ^ t * L ^ p) * L ^ w <= X := by
    calc
      (X ^ t * L ^ p) * L ^ w = X ^ t * L ^ (w + p) := by
        rw [Real.rpow_add hLPos w p]
        ring
      _ <= X ^ t * X ^ delta :=
        mul_le_mul_of_nonneg_left hLogDegree (Real.rpow_nonneg hXPos.le t)
      _ = X ^ (t + delta) := (Real.rpow_add hXPos t delta).symm
      _ <= X ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hX hGap
      _ = X := Real.rpow_one X
  calc
    X ^ t * L ^ p = (X ^ t * L ^ p) * L ^ w / L ^ w := by field_simp
    _ <= X / L ^ w := div_le_div_of_nonneg_right hProduct hWPos.le

/-- Natural numerator powers specialize the real-exponent saving transfer. -/
theorem rpow_mul_pow_le_div_of_saving {X L b t delta w : Real} (p : Nat)
    (hX : 1 <= X) (hL : 1 <= L) (hLog : L ^ b <= X ^ delta)
    (hDegree : w + (p : Real) <= b) (hGap : t + delta <= 1) :
    X ^ t * L ^ p <= X / L ^ w := by
  simpa only [Real.rpow_natCast] using
    (rpow_mul_rpow_le_div_of_saving (X := X) (L := L) (b := b) (t := t)
      (delta := delta) (w := w) (p := (p : Real)) hX hL hLog hDegree hGap)

end BombieriVinogradov.RealAnalysis
