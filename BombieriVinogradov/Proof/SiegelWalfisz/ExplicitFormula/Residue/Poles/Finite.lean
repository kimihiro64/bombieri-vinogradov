import BombieriVinogradov.Helpers.ComplexAnalysis.RectanglePoles
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.Main

/-!
# Finiteness of explicit-formula contour poles

This module specializes compact-rectangle pole finiteness to the
explicit-formula integrand and its finite contour.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The explicit-formula integrand has only finitely many poles inside every
finite source contour rectangle. -/
theorem finite_explicitFormulaIntegrand_polesInContour
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (U c T : Real) :
    (Set.inter
      (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi x) p < 0}).Finite :=
  ComplexAnalysis.finite_polesIn_rectangle (explicitFormulaIntegrand chi x)
    (explicitFormulaContourLowerLeft U T)
    (explicitFormulaContourUpperRight c T)
    (meromorphicOn_explicitFormulaIntegrand hchi x hx _)

end BombieriVinogradov.SiegelWalfisz
