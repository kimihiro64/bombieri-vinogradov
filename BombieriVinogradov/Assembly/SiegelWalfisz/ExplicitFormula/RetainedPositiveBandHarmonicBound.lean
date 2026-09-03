import BombieriVinogradov.Helpers.RealAnalysis.HarmonicLogSquare
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Modulus-aware logarithmic harmonic bound

This module specializes the reusable logarithmic harmonic estimate at log N
and factors a nonnegative absolute band constant through the finite sum.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_scaled_log_add_div_Ico_le_sq
    {C : Real} (hC : 0 <= C)
    {N : Nat} (hN : 3 <= N) (K : Nat) :
    Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
        C * (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) <=
      C * (Real.log N + Real.log ((K : Real) + 2)) ^ 2 := by
  have hThreeReal : (3 : Real) <= (N : Real) := (Nat.cast_le).2 hN
  have hOneLeLogThree : (1 : Real) <= Real.log 3 := by
    have h := Real.le_log_one_add_of_nonneg
      (x := (2 : Real)) (by norm_num)
    norm_num at h
    exact h
  have hLogThreeLeLogN : Real.log 3 <= Real.log N :=
    Real.log_le_log (by norm_num) hThreeReal
  have hOneLeLogN : (1 : Real) <= Real.log N :=
    hOneLeLogThree.trans hLogThreeLeLogN
  have hCore :
      Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
          (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) <=
        (Real.log N + Real.log ((K : Real) + 2)) ^ 2 :=
    BombieriVinogradov.RealAnalysis.sum_log_add_div_Ico_le_sq
      hOneLeLogN K
  have hRewrite :
      Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
          C * (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) =
        C * Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
          (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) := by
    calc
      Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
          C * (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) =
        Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
          C * ((Real.log N + Real.log ((k : Real) + 2)) / (k : Real))) := by
        exact Finset.sum_congr rfl (fun k hk => by ring)
      _ = C * Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
          (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) := by
        rw [Finset.mul_sum]
  rw [hRewrite]
  exact mul_le_mul_of_nonneg_left hCore hC

end BombieriVinogradov.SiegelWalfisz
