import BombieriVinogradov.Helpers.RealAnalysis.FiniteAbelSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Equality-safe reciprocal-log Abel summation

The lower prime endpoint is separated before summation, so every remaining
logarithmic weight has a positive natural argument.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Exact partial summation for coefficients vanishing at one. -/
theorem sum_Icc_div_log_eq_abel (F : Nat -> Real) {N : Nat}
    (hN : 2 <= N) (hOne : F 1 = 0) :
    Finset.sum (Finset.Icc 2 N) (fun n => F n / Real.log (n : Real)) =
      Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
  have hAbel := sum_Ioc_mul_eq_abel F (fun n => 1 / Real.log (n : Real)) hN
  have hInitial : Finset.sum (Finset.Icc 1 2) F = F 2 := by
    norm_num [Finset.sum_Icc_succ_top, hOne]
  have hIntervals : Finset.Icc 2 N = insert 2 (Finset.Ioc 2 N) :=
    (Finset.Ioc_insert_left hN).symm
  calc
    Finset.sum (Finset.Icc 2 N) (fun n => F n / Real.log (n : Real)) =
        F 2 / Real.log ((2 : Nat) : Real) +
          Finset.sum (Finset.Ioc 2 N) (fun n => F n / Real.log (n : Real)) := by
      rw [hIntervals, Finset.sum_insert]
      simp
    _ = F 2 / Real.log ((2 : Nat) : Real) +
        Finset.sum (Finset.Ioc 2 N) (fun n => F n * (1 / Real.log (n : Real))) := by
      apply congrArg (fun z : Real => F 2 / Real.log ((2 : Nat) : Real) + z)
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = F 2 / Real.log ((2 : Nat) : Real) +
        (Finset.sum (Finset.Icc 1 N) F * (1 / Real.log (N : Real)) -
          Finset.sum (Finset.Icc 1 2) F * (1 / Real.log ((2 : Nat) : Real)) +
            Finset.sum (Finset.Ico 2 N) (fun k =>
              Finset.sum (Finset.Icc 1 k) F *
                (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) := by
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one] using hAbel
    _ = Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
      rw [hInitial]
      ring

end BombieriVinogradov.RealAnalysis
