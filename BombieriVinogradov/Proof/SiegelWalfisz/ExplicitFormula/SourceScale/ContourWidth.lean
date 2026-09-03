import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimized contour width bounds
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem abs_optimizedPerronLine_sub_neg_half_le_three
    {x : Nat} (hx : 2 < x) :
    abs (optimizedPerronLine x - (-(1 : Real) / 2)) <= 3 := by
  have hNonneg :
      0 <= optimizedPerronLine x - (-(1 : Real) / 2) := by
    linarith [optimizedPerronLine_gt_one hx]
  rw [abs_of_nonneg hNonneg]
  linarith [optimizedPerronLine_le_two hx]

theorem abs_neg_half_sub_optimizedPerronLine_le_three
    {x : Nat} (hx : 2 < x) :
    abs ((-(1 : Real) / 2) - optimizedPerronLine x) <= 3 := by
  have hNeg :
      (-(1 : Real) / 2) - optimizedPerronLine x =
        -(optimizedPerronLine x - (-(1 : Real) / 2)) := by
    ring
  rw [hNeg, abs_neg]
  exact abs_optimizedPerronLine_sub_neg_half_le_three hx

end BombieriVinogradov.SiegelWalfisz
