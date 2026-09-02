import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions

/-!
# Normalized rectangle decomposition

This module proves the algebraic orientation identity that isolates the right
vertical side of the normalized rectangle integral.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The normalized right vertical integral equals the rectangle integral plus
the normalized integral over the bottom, left, and top sides. -/
theorem VIntegral'_eq_rectangle_add_brokenBoundary
    (f : Complex -> Complex) (U c T : Real) :
    VIntegral' f c (-T) T =
      RectangleIntegral' f (explicitFormulaContourLowerLeft U T)
          (explicitFormulaContourUpperRight c T) +
        explicitFormulaBrokenBoundaryIntegral f U c T := by
  simp only [explicitFormulaContourLowerLeft,
    explicitFormulaContourUpperRight,
    explicitFormulaBrokenBoundaryIntegral, RectangleIntegral',
    RectangleIntegral, HIntegral', VIntegral']
  have hsym : HIntegral f c (-U) (-T) =
      -HIntegral f (-U) c (-T) := HIntegral_symm
  rw [hsym]
  ring

end BombieriVinogradov.SiegelWalfisz
