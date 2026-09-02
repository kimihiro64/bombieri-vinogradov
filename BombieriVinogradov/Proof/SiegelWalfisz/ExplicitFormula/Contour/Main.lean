import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Rectangle
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions

/-!
# Explicit-formula contour decomposition

This module specializes the normalized rectangle identity to the
explicit-formula integrand on the optimized Perron line.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The optimized Perron integral is exactly the residue rectangle plus the
three remaining oriented boundary segments. -/
theorem explicitFormulaVerticalIntegral_eq_rectangle_add_brokenBoundary
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (U T : Real) :
    explicitFormulaVerticalIntegral chi x (optimizedPerronLine x) T =
      RectangleIntegral' (explicitFormulaIntegrand chi x)
          (explicitFormulaContourLowerLeft U T)
          (explicitFormulaContourUpperRight (optimizedPerronLine x) T) +
        explicitFormulaBrokenBoundaryIntegral (explicitFormulaIntegrand chi x)
          U (optimizedPerronLine x) T := by
  exact VIntegral'_eq_rectangle_add_brokenBoundary
    (explicitFormulaIntegrand chi x) U (optimizedPerronLine x) T

end BombieriVinogradov.SiegelWalfisz
