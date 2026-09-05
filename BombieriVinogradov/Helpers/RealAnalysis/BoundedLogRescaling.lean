import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded logarithmic rescaling

A nonnegative endpoint bound can be rescaled uniformly over a positive bounded
interval at any positive logarithmic denominator exponent.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Rescale one nonnegative bound uniformly over a real interval starting at three. -/
theorem bounded_log_rescaling {X T A K : Real}
    (hX : 3 <= X) (hXT : X <= T) (hA : 1 <= A) (hK : 0 <= K) :
    K <= ((K + 1) * (Real.log T) ^ A) *
      (X / (Real.log X) ^ A) := by
  have hXPos : 0 < X := by linarith
  have hTPos : 0 < T := hXPos.trans_le hXT
  have hXOne : 1 <= X := by linarith
  have hLogXOne : 1 <= Real.log X := by
    have hLogThree : 1 <= Real.log (3 : Real) := by
      rw [Real.le_log_iff_exp_le (by linarith : (0 : Real) < 3)]
      exact Real.exp_one_lt_three.le
    exact hLogThree.trans (Real.log_le_log (by linarith) hX)
  have hLogOrder : Real.log X <= Real.log T :=
    Real.log_le_log hXPos hXT
  have hPower : (Real.log X) ^ A <= (Real.log T) ^ A :=
    Real.rpow_le_rpow (by linarith) hLogOrder (by linarith)
  have hPowerPos : 0 < (Real.log X) ^ A :=
    Real.rpow_pos_of_pos (by linarith) A
  have hProduct :
      (Real.log X) ^ A <= (Real.log T) ^ A * X := by
    calc
      (Real.log X) ^ A = (Real.log X) ^ A * 1 := by ring
      _ <= (Real.log T) ^ A * X :=
        mul_le_mul hPower hXOne (by linarith)
          (Real.rpow_nonneg (by linarith) A)
  have hScale :
      1 <= (Real.log T) ^ A * (X / (Real.log X) ^ A) := by
    apply le_of_mul_le_mul_right
    case a0 => exact hPowerPos
    case bc =>
      calc
        1 * (Real.log X) ^ A = (Real.log X) ^ A := by ring
        _ <= (Real.log T) ^ A * X := hProduct
        _ = ((Real.log T) ^ A * (X / (Real.log X) ^ A)) *
            (Real.log X) ^ A := by field_simp
  calc
    K <= K + 1 := by linarith
    _ = (K + 1) * 1 := by ring
    _ <= (K + 1) *
        ((Real.log T) ^ A * (X / (Real.log X) ^ A)) :=
      mul_le_mul_of_nonneg_left hScale (by linarith)
    _ = ((K + 1) * (Real.log T) ^ A) *
        (X / (Real.log X) ^ A) := by ring

end BombieriVinogradov.RealAnalysis
