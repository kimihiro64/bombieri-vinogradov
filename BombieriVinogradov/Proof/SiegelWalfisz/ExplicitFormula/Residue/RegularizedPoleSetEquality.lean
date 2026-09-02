import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.CandidateValuesInContour
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedBoundaryPoles
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.RegularizedPoleCandidateValues
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Regularized pole-set equality

This module identifies the regularized poles inside the explicit-formula
rectangle with the residue candidate values that are genuine poles.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Inside an admissible contour, restricting the regularized pole set to the
rectangle is the same as restricting it to the finite candidate-value set. -/
theorem inter_regularizedPoleSet_eq_candidateValues_inter
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
    Set.inter
      (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt
        (regularizedExplicitFormulaIntegrand chi x) rho < 0} =
    Set.inter
      (explicitFormulaResidueCandidateValues chi T exceptional : Set Complex)
      {rho | meromorphicOrderAt
        (regularizedExplicitFormulaIntegrand chi x) rho < 0} := by
  have hRe : -U <= c := by linarith
  have hBoundary : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt
        (regularizedExplicitFormulaIntegrand chi x) rho < 0} :=
    disjoint_regularizedExplicitFormulaIntegrand_poles_boundary
      hchi x hx (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T) horiginal hzero
  apply Set.ext
  intro rho
  exact Iff.intro
    (fun hrho => by
      have hrhoBorder : Not (Membership.mem
          (RectangleBorder (explicitFormulaContourLowerLeft U T)
            (explicitFormulaContourUpperRight c T)) rho) := by
        intro hOnBorder
        exact Set.disjoint_left.mp hBoundary hOnBorder hrho.2
      exact And.intro
        (mem_residueCandidateValues_of_regularized_pole
          hchi hPrimitive x hx U c T hULt hT hRe exceptional
          hrho.1 hrhoBorder hrho.2)
        hrho.2)
    (fun hrho =>
      And.intro
        (mem_explicitFormulaContour_of_mem_residueCandidateValues
          hUNonneg hc hT hChoice hrho.1)
        hrho.2)

end BombieriVinogradov.SiegelWalfisz
