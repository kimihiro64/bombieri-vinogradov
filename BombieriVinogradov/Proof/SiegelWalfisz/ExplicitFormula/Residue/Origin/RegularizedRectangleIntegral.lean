import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.CorrectionBorderIntegrable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.CorrectionRectangleIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Equality of original and regularized rectangle integrals

This module composes correction integrability and correction vanishing to
show that origin regularization preserves the normalized contour integral.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Adding the origin correction does not change the normalized rectangle
integral when the original integrand is border-integrable and the border
avoids zero. -/
theorem rectangleIntegral'_regularizedExplicitFormulaIntegrand_eq
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (z w : Complex)
    (horiginal :
      RectangleBorderIntegrable (explicitFormulaIntegrand chi x) z w)
    (hzero : Not (Membership.mem (RectangleBorder z w) 0)) :
    RectangleIntegral' (regularizedExplicitFormulaIntegrand chi x) z w =
      RectangleIntegral' (explicitFormulaIntegrand chi x) z w := by
  have hcorrectionBorder :=
    rectangleBorderIntegrable_originDoublePoleCorrection chi z w hzero
  have hcorrectionIntegral :=
    rectangleIntegral'_originDoublePoleCorrection_eq_zero chi z w hzero
  have hadd :
      RectangleIntegral'
          ((explicitFormulaIntegrand chi x) + originDoublePoleCorrection chi)
          z w =
        RectangleIntegral' (explicitFormulaIntegrand chi x) z w +
          RectangleIntegral' (originDoublePoleCorrection chi) z w := by
    unfold RectangleIntegral'
    rw [horiginal.add hcorrectionBorder, smul_add]
  change RectangleIntegral'
      ((explicitFormulaIntegrand chi x) + originDoublePoleCorrection chi)
      z w = RectangleIntegral' (explicitFormulaIntegrand chi x) z w
  rw [hadd, hcorrectionIntegral, add_zero]

end BombieriVinogradov.SiegelWalfisz
