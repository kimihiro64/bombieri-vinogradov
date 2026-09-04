import BombieriVinogradov.Helpers.RealAnalysis.HarmonicIcc
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Shifted harmonic sums on positive intervals

A reciprocal Abel kernel's linear term is bounded by the full harmonic sum.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A shifted reciprocal sum below Q costs at most one plus log Q. -/
theorem sum_one_div_add_one_Ico_le {R Q : Nat} (hR : 1 <= R) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) <=
      1 + Real.log (Q : Real) := by
  have hSubset : forall k, (Finset.Ico R Q : Set Nat) k ->
      (Finset.Icc 1 Q : Set Nat) k := by
    intro k hk
    exact Finset.mem_Icc.mpr (And.intro (hR.trans (Finset.mem_Ico.mp hk).1)
      (Finset.mem_Ico.mp hk).2.le)
  calc
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) <=
        Finset.sum (Finset.Ico R Q) (fun k => 1 / (k : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hR.trans (Finset.mem_Ico.mp hk).1)
      have hkReal : (0 : Real) < (k : Real) := Nat.cast_pos.mpr hkPos
      exact one_div_le_one_div_of_le hkReal (by linarith)
    _ <= Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k : Real)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun k _ _ => by positivity)
    _ <= 1 + Real.log (Q : Real) := sum_one_div_Icc_le_one_add_log Q

end BombieriVinogradov.RealAnalysis
