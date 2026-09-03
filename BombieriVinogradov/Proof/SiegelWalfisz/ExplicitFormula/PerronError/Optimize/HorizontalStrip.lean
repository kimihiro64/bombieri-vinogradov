import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.Linarith

/-!
# Real-part bounds on the optimized horizontal strip

This module isolates the unordered-interval geometry shared by the top and
bottom optimized horizontal contour segments.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem mem_optimizedHorizontalStrip_bounds
    {x : Nat} (hx : 2 < x) {u : Real}
    (hu : Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u) :
    And (-(1 : Real) / 2 <= u) (u <= 2) := by
  have hLineLower :
      -(1 : Real) / 2 <= optimizedPerronLine x := by
    linarith [optimizedPerronLine_gt_one hx]
  have huBounds :
      Set.Icc (-(1 : Real) / 2) (optimizedPerronLine x) u := by
    simpa [Set.uIcc_of_le hLineLower] using hu
  exact And.intro huBounds.1
    (huBounds.2.trans (optimizedPerronLine_le_two hx))

end BombieriVinogradov.SiegelWalfisz
