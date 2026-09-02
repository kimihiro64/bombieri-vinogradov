import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedRectangleIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedResidueTheorem
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.BorderIntegrable
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Original contour residue identity

This module composes border integrability and origin regularization with the
rectangle residue theorem. Individual residue evaluation remains separate.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The original explicit-formula contour integral equals the residue sum of
the simple-pole origin-regularized integrand on every admissible rectangle. -/
theorem rectangleIntegral'_explicitFormulaIntegrand_eq_sumResiduesIn_regularized
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (z w : Complex)
    (hre : z.re <= w.re) (him : z.im <= w.im)
    (hpoles : Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi x) p < 0})
    (hzero : Not (Membership.mem (RectangleBorder z w) 0)) :
    RectangleIntegral' (explicitFormulaIntegrand chi x) z w =
      sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
        (Set.inter (Complex.Rectangle z w)
          {p | meromorphicOrderAt
            (regularizedExplicitFormulaIntegrand chi x) p < 0}) := by
  have hBorder :
      RectangleBorderIntegrable (explicitFormulaIntegrand chi x) z w :=
    rectangleBorderIntegrable_explicitFormulaIntegrand
      hchi x hx z w hpoles
  calc
    RectangleIntegral' (explicitFormulaIntegrand chi x) z w =
        RectangleIntegral' (regularizedExplicitFormulaIntegrand chi x) z w :=
      (rectangleIntegral'_regularizedExplicitFormulaIntegrand_eq
        chi x z w hBorder hzero).symm
    _ = sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
        (Set.inter (Complex.Rectangle z w)
          {p | meromorphicOrderAt
            (regularizedExplicitFormulaIntegrand chi x) p < 0}) :=
      rectangleIntegral'_regularizedExplicitFormulaIntegrand_eq_sumResiduesIn
        hchi x hx z w hre him hpoles hzero

end BombieriVinogradov.SiegelWalfisz
