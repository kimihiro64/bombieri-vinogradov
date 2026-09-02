import BombieriVinogradov.Helpers.ComplexAnalysis.RectanglePoles
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedMeromorphic

/-!
# Finiteness of regularized contour poles

This module specializes compact-rectangle pole finiteness to the
origin-regularized explicit-formula integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The regularized explicit-formula integrand has only finitely many poles
inside every closed complex rectangle. -/
theorem finite_regularizedExplicitFormulaIntegrand_polesInRectangle
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (z w : Complex) :
    (Set.inter (Complex.Rectangle z w)
      {p | meromorphicOrderAt
        (regularizedExplicitFormulaIntegrand chi x) p < 0}).Finite :=
  BombieriVinogradov.ComplexAnalysis.finite_polesIn_rectangle
    (regularizedExplicitFormulaIntegrand chi x) z w
    (meromorphic_regularizedExplicitFormulaIntegrand hchi x hx).meromorphicOn

end BombieriVinogradov.SiegelWalfisz
