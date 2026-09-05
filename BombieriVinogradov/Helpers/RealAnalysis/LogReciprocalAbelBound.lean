import BombieriVinogradov.Helpers.RealAnalysis.LogReciprocalAbel
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounding reciprocal-log Abel summation

Positive logarithmic differences telescope exactly, so a uniform cumulative
bound loses only the fixed factor one over log two.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Reciprocal logarithms decrease on natural arguments at least two. -/
theorem log_reciprocal_difference_nonneg {k : Nat} (hk : 2 <= k) :
    0 <= 1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1) := by
  have hkPos : (0 : Real) < (k : Real) := by positivity
  have hLogPos : 0 < Real.log (k : Real) := Real.log_pos (by
    have hkCast : (2 : Real) <= (k : Real) := Nat.cast_le.mpr hk
    linarith)
  have hLogLe : Real.log (k : Real) <= Real.log ((k : Real) + 1) :=
    Real.log_le_log hkPos (by linarith)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hLogPos hLogLe)

/-- The positive reciprocal-log differences telescope. -/
theorem sum_log_reciprocal_differences {N : Nat} (hN : 2 <= N) :
    Finset.sum (Finset.Ico 2 N) (fun k =>
      1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)) =
        1 / Real.log (2 : Real) - 1 / Real.log (N : Real) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- A uniform cumulative bound controls the reciprocal-log weighted sum. -/
theorem abs_sum_Icc_div_log_le (F : Nat -> Real) {N : Nat} {D : Real}
    (hN : 2 <= N) (hOne : F 1 = 0)
    (hBound : forall k : Nat, 1 <= k -> k <= N ->
      abs (Finset.sum (Finset.Icc 1 k) F) <= D) :
    abs (Finset.sum (Finset.Icc 2 N) (fun n => F n / Real.log (n : Real))) <=
      D / Real.log (2 : Real) := by
  have hLogN : 0 < Real.log (N : Real) := Real.log_pos (by
    have hNCast : (2 : Real) <= (N : Real) := Nat.cast_le.mpr hN
    linarith)
  rw [sum_Icc_div_log_eq_abel F hN hOne]
  calc
    abs (Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) <=
      abs (Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real)) +
        abs (Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) :=
      abs_add_le _ _
    _ <= D / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          D * (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
      exact add_le_add (by
        rw [abs_div, abs_of_pos hLogN]
        exact div_le_div_of_nonneg_right
          (hBound N (by linarith) (le_refl N)) hLogN.le) (by
        calc
          abs (Finset.sum (Finset.Ico 2 N) (fun k =>
              Finset.sum (Finset.Icc 1 k) F *
                (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) <=
            Finset.sum (Finset.Ico 2 N) (fun k =>
              abs (Finset.sum (Finset.Icc 1 k) F *
                (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) :=
              Finset.abs_sum_le_sum_abs _ _
          _ <= Finset.sum (Finset.Ico 2 N) (fun k =>
              D * (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkData := Finset.mem_Ico.mp hk
            have hDiff := log_reciprocal_difference_nonneg hkData.1
            rw [abs_mul, abs_of_nonneg hDiff]
            exact mul_le_mul_of_nonneg_right
              (hBound k (by linarith) hkData.2.le) hDiff)
    _ = D / Real.log (2 : Real) := by
      rw [show Finset.sum (Finset.Ico 2 N) (fun k =>
        D * (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) =
          D * Finset.sum (Finset.Ico 2 N) (fun k =>
            1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)) by
              exact (Finset.mul_sum _ _ _).symm,
        sum_log_reciprocal_differences hN]
      ring

end BombieriVinogradov.RealAnalysis
