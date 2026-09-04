import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.FieldSimp

/-!
# Finite averages with a cardinality majorant

A common nonnegative bound survives division by any positive quantity that
dominates the number of summands. The summands themselves may be negative.
-/

set_option autoImplicit false

universe u

namespace BombieriVinogradov.RealAnalysis

/-- A finite sum divided by a positive cardinality majorant preserves a common bound. -/
theorem sum_div_le_of_card_le {I : Type u} (s : Finset I) (f : I -> Real)
    {t K : Real} (ht : 0 < t) (hCard : (s.card : Real) <= t)
    (hK : 0 <= K) (hf : forall i, (s : Set I) i -> f i <= K) :
    Finset.sum s f / t <= K := by
  have hSum : Finset.sum s f <= t * K := by
    calc
      Finset.sum s f <= Finset.sum s (fun _ => K) :=
        Finset.sum_le_sum (fun i hi => hf i hi)
      _ = (s.card : Real) * K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ <= t * K := mul_le_mul_of_nonneg_right hCard hK
  calc
    Finset.sum s f / t <= t * K / t := div_le_div_of_nonneg_right hSum ht.le
    _ = K := by field_simp

end BombieriVinogradov.RealAnalysis
