import BombieriVinogradov.Helpers.RealAnalysis.QuadraticAbelKernel
import BombieriVinogradov.Helpers.RealAnalysis.ReciprocalKernelSum
import BombieriVinogradov.Helpers.RealAnalysis.ShiftedHarmonicIco
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Summing a quadratic majorant against the Abel kernel

The constant, linear and quadratic parts use telescoping, harmonic comparison
and interval cardinality respectively.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A quadratic cumulative majorant has a controlled reciprocal Abel kernel sum. -/
theorem sum_quadratic_div_reciprocal_kernel_le (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) {R Q : Nat}
    (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) <=
      a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real) := by
  have hCard : ((Finset.Ico R Q).card : Real) <= (Q : Real) := by
    rw [Nat.card_Ico]
    exact Nat.cast_le.mpr (Nat.sub_le Q R)
  have hConstant := mul_le_mul_of_nonneg_left
    (sum_reciprocal_product_Ico_le hR hRQ) ha
  have hLinear := mul_le_mul_of_nonneg_left
    (sum_one_div_add_one_Ico_le (Q := Q) hR) hb
  have hQuadratic := mul_le_mul_of_nonneg_right hCard hc
  calc
    Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) <=
        Finset.sum (Finset.Ico R Q)
          (fun k => a / ((k : Real) * ((k : Real) + 1)) +
            b / ((k : Real) + 1) + c) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hR.trans (Finset.mem_Ico.mp hk).1)
      exact quadratic_div_reciprocal_kernel_le a b c (k : Real) hc
        (Nat.cast_pos.mpr hkPos)
    _ = a * Finset.sum (Finset.Ico R Q)
          (fun k => 1 / ((k : Real) * ((k : Real) + 1))) +
        b * Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) +
        ((Finset.Ico R Q).card : Real) * c := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.mul_sum, mul_one_div]
    _ <= a * (1 / (R : Real)) + b * (1 + Real.log (Q : Real)) + (Q : Real) * c :=
      add_le_add (add_le_add hConstant hLinear) hQuadratic
    _ = a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real) := by
      rw [mul_one_div]
      ring

end BombieriVinogradov.RealAnalysis
