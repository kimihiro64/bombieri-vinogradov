import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Real bound for the integer base-two logarithm

The defining lower power bound for Nat.log gives a real logarithmic
upper bound for the complete prime-power exponent cutoff.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem natLog_two_le_real_log_div {x : Nat} (hx : 0 < x) :
    (Nat.log 2 x : Real) <= Real.log x / Real.log (2 : Real) := by
  have hxNe : Ne x 0 := by omega
  have hPower : 2 ^ Nat.log 2 x <= x := Nat.pow_log_le_self 2 hxNe
  have hRaw : ((2 ^ Nat.log 2 x : Nat) : Real) <= (x : Real) :=
    Nat.cast_le.mpr hPower
  norm_num only [Nat.cast_pow] at hRaw
  have hLogPower : Real.log ((2 : Real) ^ Nat.log 2 x) <= Real.log x :=
    Real.log_le_log (by positivity) hRaw
  rw [Real.log_pow] at hLogPower
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogTwoNe : Ne (Real.log (2 : Real)) 0 := by linarith
  have hCancel :
      (Real.log x / Real.log (2 : Real)) * Real.log (2 : Real) = Real.log x := by
    field_simp [hLogTwoNe]
  nlinarith

end BombieriVinogradov.RealAnalysis
