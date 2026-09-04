import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Summed logarithmic modulus correction

The finite Euler-factor correction sums to at most Q log Q log X / log 2.
The empty modulus range and X = 1 are included.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Bound the sum of logarithmic corrections by its maximum times the modulus count. -/
theorem sum_log_mul_log_div_log_two_le (Q : Nat) {X : Real} (hX : 1 <= X) :
    Finset.sum (Finset.Icc 1 Q)
        (fun q => Real.log q * Real.log X / Real.log (2 : Real)) <=
      (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) := by
  have hLogX : 0 <= Real.log X := Real.log_nonneg hX
  have hLogTwo : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  calc
    Finset.sum (Finset.Icc 1 Q)
        (fun q => Real.log q * Real.log X / Real.log (2 : Real)) <=
        Finset.sum (Finset.Icc 1 Q)
          (fun _ => Real.log Q * Real.log X / Real.log (2 : Real)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : 0 < q :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
      have hCast : (q : Real) <= (Q : Real) :=
        Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2
      have hLog : Real.log q <= Real.log Q :=
        Real.log_le_log (Nat.cast_pos.mpr hqPos) hCast
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLog hLogX) hLogTwo
    _ = (Q : Real) * (Real.log Q * Real.log X / Real.log (2 : Real)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ = (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) := by ring

end BombieriVinogradov.RealAnalysis
