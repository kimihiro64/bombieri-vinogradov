import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# One positive rate for the character estimates

Choose the rate before every modulus and endpoint, while reserving
enough of the zero-free gap and the source-remainder exponential rate.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exists_positive_small_decay_rate {c : Real} (hc : 0 < c) :
    exists a : Real, And (0 < a)
      (And (a <= (1 / 2 : Real)) (2 * a <= c / 4)) := by
  refine Exists.intro (min (c / 8) (1 / 2 : Real))
    (And.intro (by positivity) (And.intro (min_le_right _ _) ?_))
  have h := min_le_left (c / 8) (1 / 2 : Real)
  linarith

end BombieriVinogradov.RealAnalysis
