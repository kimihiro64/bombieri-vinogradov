import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedMeromorphic
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.RegularizedPoleSetEquality
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Transfer of the regularized residue sum to candidate values

This module moves the contour residue sum onto the finite candidate-value set.
Residue decomposition is deliberately left to a separate module.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The regularized residue sum over the contour poles equals the residue sum
over all finite candidate values; nonpoles contribute zero. -/
theorem sumResiduesIn_regularizedContour_eq_candidateValues
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) (c0 U c T : Real)
    (hUNonneg : 0 <= U) (hULt : U < 1) (hc : 1 <= c) (hT : 0 < T)
    (exceptional : Option Complex)
    (hChoice : IsExceptionalZeroChoice c0 chi exceptional)
    (horiginal : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt (explicitFormulaIntegrand chi x) rho < 0})
    (hzero : Not (Membership.mem
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) 0)) :
    sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
      (Set.inter
        (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
          (explicitFormulaContourUpperRight c T))
        {rho | meromorphicOrderAt
          (regularizedExplicitFormulaIntegrand chi x) rho < 0}) =
    sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
      (explicitFormulaResidueCandidateValues chi T exceptional : Set Complex) := by
  exact sumResiduesIn_inter_eq_of_set_eq
    (inter_regularizedPoleSet_eq_candidateValues_inter
      hchi hPrimitive x hx c0 U c T hUNonneg hULt hc hT exceptional
      hChoice horiginal hzero)
    (fun rho _ hrhoNotPole =>
      residue_eq_zero_of_not_pole_of_meromorphicAt
        (meromorphic_regularizedExplicitFormulaIntegrand hchi x hx rho)
        (le_of_not_gt hrhoNotPole))

end BombieriVinogradov.SiegelWalfisz
