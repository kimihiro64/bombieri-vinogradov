import BombieriVinogradov.Helpers.RealAnalysis.ReciprocalDifference
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal Abel kernel sums

Consecutive reciprocal differences telescope on positive half-open intervals.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- The reciprocal product kernel telescopes, including equal cutoffs. -/
theorem sum_reciprocal_product_Ico {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) * ((k : Real) + 1))) =
      1 / (R : Real) - 1 / (Q : Real) := by
  induction Q, hRQ using Nat.le_induction with
  | base => simp
  | succ Q hRQ ih =>
    have hQ : 0 < Q := Nat.lt_of_lt_of_le Nat.zero_lt_one (hR.trans hRQ)
    have hQReal : (0 : Real) < (Q : Real) := Nat.cast_pos.mpr hQ
    have hDiff : 1 / (Q : Real) - 1 / ((Q : Real) + 1) =
        1 / ((Q : Real) * ((Q : Real) + 1)) := by
      simpa only [one_mul] using mul_sub_reciprocal_eq_div_mul 1 (Q : Real)
        (by positivity) (by positivity)
    rw [Finset.sum_Ico_succ_top hRQ, ih, <- hDiff]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- The positive reciprocal kernel has total mass at most the inverse lower cutoff. -/
theorem sum_reciprocal_product_Ico_le {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) * ((k : Real) + 1))) <=
      1 / (R : Real) := by
  rw [sum_reciprocal_product_Ico hR hRQ]
  have hInv : (0 : Real) <= 1 / (Q : Real) := by positivity
  linarith

end BombieriVinogradov.RealAnalysis
