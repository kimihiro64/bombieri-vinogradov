import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Monotonicity of the source remainder in the character level

Increasing the positive level increases its nonnegative product logarithm.
The secondary quarter-power term is unchanged.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem explicitFormulaRemainderMajorant_mono_level
    {d N x : Nat} (hd : 3 <= d) (hdN : d <= N) (hx : 2 <= x)
    {T : Real} (hT : 2 <= T) :
    explicitFormulaRemainderMajorant d x T <=
      explicitFormulaRemainderMajorant N x T := by
  have hProductPos : 0 < ((d * x : Nat) : Real) :=
    Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))
  have hProductLe : ((d * x : Nat) : Real) <= ((N * x : Nat) : Real) :=
    Nat.cast_le.mpr (Nat.mul_le_mul_right x hdN)
  have hLogLe := Real.log_le_log hProductPos hProductLe
  have hdLogNonneg := Real.log_natCast_nonneg (d * x)
  have hNLogNonneg := Real.log_natCast_nonneg (N * x)
  have hSquareProduct : 0 <=
      (Real.log ((N * x : Nat) : Real) - Real.log ((d * x : Nat) : Real)) *
        (Real.log ((N * x : Nat) : Real) + Real.log ((d * x : Nat) : Real)) :=
    mul_nonneg (by linarith) (by linarith)
  have hSquareLe : (Real.log ((d * x : Nat) : Real)) ^ 2 <=
      (Real.log ((N * x : Nat) : Real)) ^ 2 := by nlinarith
  have hRatioNonneg : 0 <= (x : Real) / T :=
    div_nonneg (Nat.cast_nonneg x) (by linarith)
  have hPrimary := mul_le_mul_of_nonneg_left hSquareLe hRatioNonneg
  unfold explicitFormulaRemainderMajorant
  linarith

end BombieriVinogradov.SiegelWalfisz
