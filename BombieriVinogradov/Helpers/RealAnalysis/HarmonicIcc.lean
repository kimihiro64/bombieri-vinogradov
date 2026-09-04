import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Logarithmic bound for a positive inclusive reciprocal sum

The natural interval convention is transported exactly to the
rational harmonic number before applying its real logarithmic bound.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem sum_one_div_Icc_le_one_add_log (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) <=
      1 + Real.log (Q : Real) := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) = (harmonic Q : Real) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
    _ <= 1 + Real.log (Q : Real) := harmonic_le_one_add_log Q

end BombieriVinogradov.RealAnalysis
