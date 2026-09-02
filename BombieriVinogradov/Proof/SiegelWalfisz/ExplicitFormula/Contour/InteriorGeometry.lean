import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import PrimeNumberTheoremAnd.Rectangle

/-!
# Interior geometry of the explicit-formula contour

This module extracts the strict source-strip inequalities from membership in
the closed contour rectangle together with exclusion from its border.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- An interior point of an admissible explicit-formula contour lies to the
right of real part minus one and strictly below the truncation height. -/
theorem neg_one_lt_re_and_abs_im_lt_of_mem_explicitFormulaContour
    (U c T : Real) (hU : U < 1) (hT : 0 < T) (hRe : -U <= c)
    {rho : Complex}
    (hrhoRect : Membership.mem
      (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) rho)
    (hrhoBorder : Not (Membership.mem
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) rho)) :
    And (-1 < rho.re) (abs rho.im < T) := by
  have hCornersRe :
      (explicitFormulaContourLowerLeft U T).re <=
        (explicitFormulaContourUpperRight c T).re := by
    simpa [explicitFormulaContourLowerLeft,
      explicitFormulaContourUpperRight] using hRe
  have hCornersIm :
      (explicitFormulaContourLowerLeft U T).im <=
        (explicitFormulaContourUpperRight c T).im := by
    change -T <= T
    linarith
  have hcoords :=
    (mem_Rect hCornersRe hCornersIm rho).mp hrhoRect
  have hLeft : -U <= rho.re := by
    simpa [explicitFormulaContourLowerLeft] using hcoords.1
  have hLower : -1 < rho.re := by linarith
  have hImBounds : And (-T <= rho.im) (rho.im <= T) := by
    exact And.intro
      (by simpa [explicitFormulaContourLowerLeft] using hcoords.2.2.1)
      (by simpa [explicitFormulaContourUpperRight] using hcoords.2.2.2)
  have hReMem : Membership.mem
      (Set.uIcc (explicitFormulaContourLowerLeft U T).re
        (explicitFormulaContourUpperRight c T).re) rho.re := by
    rw [Set.uIcc_of_le hCornersRe]
    exact And.intro hcoords.1 hcoords.2.1
  have hBottomNe : Ne rho.im (-T) := by
    intro hEq
    apply hrhoBorder
    rw [RectangleBorder]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply And.intro hReMem
    have hBottomEq :
        rho.im = (explicitFormulaContourLowerLeft U T).im := by
      simpa [explicitFormulaContourLowerLeft] using hEq
    exact Set.mem_singleton_iff.mpr hBottomEq
  have hTopNe : Ne rho.im T := by
    intro hEq
    apply hrhoBorder
    rw [RectangleBorder]
    apply Or.inl
    apply Or.inr
    apply And.intro hReMem
    have hTopEq :
        rho.im = (explicitFormulaContourUpperRight c T).im := by
      simpa [explicitFormulaContourUpperRight] using hEq
    exact Set.mem_singleton_iff.mpr hTopEq
  have hImLower : -T < rho.im :=
    lt_of_le_of_ne hImBounds.1 (Ne.symm hBottomNe)
  have hImUpper : rho.im < T :=
    lt_of_le_of_ne hImBounds.2 hTopNe
  exact And.intro hLower (abs_lt.mpr (And.intro hImLower hImUpper))

end BombieriVinogradov.SiegelWalfisz
