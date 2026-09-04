import BombieriVinogradov.Helpers.RealAnalysis.QuadraticAbelBoundary
import BombieriVinogradov.Helpers.RealAnalysis.QuadraticAbelKernelSum
import BombieriVinogradov.Helpers.RealAnalysis.ReciprocalAbelSum
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal tails from quadratic cumulative bounds

The finite Abel identity retains all boundary and kernel contributions.
A common multiplier remains on every term of the resulting estimate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A nonnegative sequence with a quadratic cumulative bound has a reciprocal tail bound. -/
theorem sum_Ioc_div_le_of_quadratic_partial_sums (F : Nat -> Real) (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hF : forall n, 0 <= F n)
    {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q)
    (hBound : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <= a + b * (k : Real) + c * (k : Real) ^ 2) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
      2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) + 2 * c * (Q : Real) := by
  have hRReal : (0 : Real) < (R : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hR)
  have hRQReal : (R : Real) <= (Q : Real) := Nat.cast_le.mpr hRQ
  have hBoundary : Finset.sum (Finset.Icc 1 Q) F / (Q : Real) <=
      a / (R : Real) + b + c * (Q : Real) :=
    (div_le_div_of_nonneg_right (hBound Q (hR.trans hRQ) (Nat.le_refl Q))
      (Nat.cast_nonneg Q)).trans
      (quadratic_div_boundary_le a b c (Q : Real) (R : Real) ha hRReal hRQReal)
  have hKernel :
      Finset.sum (Finset.Ico R Q)
        (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) <=
      Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact div_le_div_of_nonneg_right
      (hBound k (hR.trans (Finset.mem_Ico.mp hk).1) (Finset.mem_Ico.mp hk).2.le)
      (by positivity)
  have hKernelBound := hKernel.trans
    (sum_quadratic_div_reciprocal_kernel_le a b c ha hb hc hR hRQ)
  have hDiscard : 0 <= Finset.sum (Finset.Icc 1 R) F / (R : Real) :=
    div_nonneg (Finset.sum_nonneg (fun n _ => hF n)) (Nat.cast_nonneg R)
  rw [sum_Ioc_div_eq_abel F hR hRQ]
  calc
    Finset.sum (Finset.Icc 1 Q) F / (Q : Real) -
        Finset.sum (Finset.Icc 1 R) F / (R : Real) +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) <=
        (a / (R : Real) + b + c * (Q : Real)) +
          (a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real)) := by
      linarith
    _ = 2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real) := by ring

/-- Preserve a common cumulative multiplier on every reciprocal-tail contribution. -/
theorem sum_Ioc_div_le_of_scaled_quadratic_partial_sums
    (F : Nat -> Real) (L a b c : Real) (hL : 0 <= L)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hF : forall n, 0 <= F n)
    {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q)
    (hBound : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <= L * (a + b * (k : Real) + c * (k : Real) ^ 2)) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
      L * (2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real)) := by
  have hScaled : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <=
        L * a + (L * b) * (k : Real) + (L * c) * (k : Real) ^ 2 := by
    intro k hk hkQ
    calc
      Finset.sum (Finset.Icc 1 k) F <=
          L * (a + b * (k : Real) + c * (k : Real) ^ 2) := hBound k hk hkQ
      _ = L * a + (L * b) * (k : Real) + (L * c) * (k : Real) ^ 2 := by ring
  calc
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
        2 * (L * a) / (R : Real) + (L * b) * (2 + Real.log (Q : Real)) +
          2 * (L * c) * (Q : Real) :=
      sum_Ioc_div_le_of_quadratic_partial_sums F (L * a) (L * b) (L * c)
        (by positivity) (by positivity) (by positivity) hF hR hRQ hScaled
    _ = L * (2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real)) := by ring

end BombieriVinogradov.RealAnalysis
