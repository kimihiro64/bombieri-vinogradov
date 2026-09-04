import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A finite average with one additional uniform error

The index count and the extra error sum to exactly the positive
normalizing scale. No sign restriction on the common error is needed.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem sum_div_add_error_div_le_sum_div_add_error
    {I : Type} (s : Finset I) (f g : I -> Real) {B t : Real}
    (ht : 0 < t) (hCard : (s.card : Real) + 1 = t)
    (hfg : forall i : I, (s : Set I) i -> f i <= g i + B) :
    Finset.sum s f / t + B / t <= Finset.sum s g / t + B := by
  have hSum := Finset.sum_le_sum hfg
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hSum
  have hDiv := div_le_div_of_nonneg_right hSum ht.le
  have hCancel : t * B / t = B := by field_simp
  calc
    Finset.sum s f / t + B / t <=
        (Finset.sum s g + (s.card : Real) * B) / t + B / t :=
      add_le_add hDiv (le_refl _)
    _ = Finset.sum s g / t + ((s.card : Real) + 1) * B / t := by ring
    _ = Finset.sum s g / t + B := by rw [hCard, hCancel]

end BombieriVinogradov.RealAnalysis
