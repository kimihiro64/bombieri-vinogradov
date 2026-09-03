import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import Mathlib.Tactic.NormNum
import PrimeNumberTheoremAnd.Rectangle

/-!
# Zero avoidance on the optimized explicit-formula contour

This module proves that the origin lies on none of the four sides of the
positive-height rectangle used for the centered contour identity.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem zero_not_mem_optimizedExplicitFormulaContourBorder
    {x : Nat} (hx : 2 < x) {T : Real} (hT : 0 < T) :
    Not ((RectangleBorder
      (explicitFormulaContourLowerLeft ((1 : Real) / 2) T)
      (explicitFormulaContourUpperRight (optimizedPerronLine x) T)) 0) := by
  have hDisjoint : Disjoint
      (RectangleBorder
        (explicitFormulaContourLowerLeft ((1 : Real) / 2) T)
        (explicitFormulaContourUpperRight (optimizedPerronLine x) T))
      {0} := by
    apply rectangleBorder_disjoint_singleton
    dsimp [explicitFormulaContourLowerLeft,
      explicitFormulaContourUpperRight]
    exact And.intro (by norm_num)
      (And.intro
        (ne_of_lt (zero_lt_one.trans (optimizedPerronLine_gt_one hx)))
        (And.intro
          (Ne.symm (neg_ne_zero.mpr (ne_of_gt hT)))
          (ne_of_lt hT)))
  intro hBorder
  exact Set.disjoint_left.mp hDisjoint hBorder rfl

end BombieriVinogradov.SiegelWalfisz
