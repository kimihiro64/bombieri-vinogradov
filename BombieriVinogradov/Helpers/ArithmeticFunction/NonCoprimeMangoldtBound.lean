import BombieriVinogradov.Helpers.ArithmeticFunction.NonCoprimeMangoldtIntegerBound
import BombieriVinogradov.Helpers.RealAnalysis.NatLogarithm
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Real-logarithmic bound for the noncoprime Mangoldt mass

Convert the complete integer cutoff in the divisor bound to a real logarithm.
The coefficient is absolute and independent of the modulus and endpoint.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem nonCoprimeMangoldtSum_le_log_mul_log
    {N x : Nat} (hN : Ne N 0) (hx : 0 < x) :
    Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
      ArithmeticFunction.vonMangoldt <=
        Real.log N * Real.log x / Real.log (2 : Real) := by
  calc
    Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
        ArithmeticFunction.vonMangoldt <=
          (Nat.log 2 x : Real) * Real.log N :=
      nonCoprimeMangoldtSum_le_natLog_mul_log hN x
    _ <= (Real.log x / Real.log (2 : Real)) * Real.log N :=
      mul_le_mul_of_nonneg_right (RealAnalysis.natLog_two_le_real_log_div hx)
        (Real.log_natCast_nonneg N)
    _ = Real.log N * Real.log x / Real.log (2 : Real) := by ring

end BombieriVinogradov
