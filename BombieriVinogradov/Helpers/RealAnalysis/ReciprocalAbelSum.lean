import BombieriVinogradov.Helpers.RealAnalysis.FiniteAbelSum
import BombieriVinogradov.Helpers.RealAnalysis.ReciprocalDifference
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Positivity

/-!
# Reciprocal Abel summation

The exact discrete identity used to turn cumulative character means into
reciprocal-weighted tails. No sign condition is imposed on the coefficients.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Equality-safe reciprocal summation by parts on a positive natural interval. -/
theorem sum_Ioc_div_eq_abel (F : Nat -> Real) {R Q : Nat}
    (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) =
      Finset.sum (Finset.Icc 1 Q) F / (Q : Real) -
        Finset.sum (Finset.Icc 1 R) F / (R : Real) +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) := by
  have hAbel := sum_Ioc_mul_eq_abel F (fun n => 1 / (n : Real)) hRQ
  simp only [mul_one_div] at hAbel
  rw [hAbel]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (hR.trans (Finset.mem_Ico.mp hk).1)
  have hkReal : (0 : Real) < (k : Real) := Nat.cast_pos.mpr hkPos
  simp only [Nat.cast_add, Nat.cast_one]
  exact mul_sub_reciprocal_eq_div_mul (Finset.sum (Finset.Icc 1 k) F) (k : Real)
    (by positivity) (by positivity)

end BombieriVinogradov.RealAnalysis
