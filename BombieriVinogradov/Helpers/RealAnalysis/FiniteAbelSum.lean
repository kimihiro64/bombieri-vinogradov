import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Ring

/-!
# Finite Abel summation with equality-safe endpoints

The lower boundary uses the same weight as the cumulative sum there.
The correction interval is half-open, so equal cutoffs cancel exactly.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Finite summation by parts, including an empty interval and signed coefficients. -/
theorem sum_Ioc_mul_eq_abel (F g : Nat -> Real) {R Q : Nat} (hRQ : R <= Q) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n * g n) =
      Finset.sum (Finset.Icc 1 Q) F * g Q -
        Finset.sum (Finset.Icc 1 R) F * g R +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F * (g k - g (k + 1))) := by
  induction Q, hRQ using Nat.le_induction with
  | base => simp
  | succ Q hRQ ih =>
    rw [Finset.sum_Ioc_succ_top hRQ, Finset.sum_Ico_succ_top hRQ,
      Finset.sum_Icc_succ_top (Nat.succ_pos Q), ih]
    ring

end BombieriVinogradov.RealAnalysis
