import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ContourResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.RegularizedResidueDecomposition
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.Rectangle
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered contour residue decomposition

This module subtracts the x equals one residue identity from the x identity.
The finite origin logarithmic-derivative value cancels exactly.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered contour residue sum contains only the origin multiplicity
logarithm and the centered retained and exceptional zero contributions. -/
theorem centeredRegularizedContourResidueSum_eq_decomposed
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) (c0 U c T : Real)
    (hUNonneg : 0 <= U) (hULt : U < 1) (hc : 1 <= c) (hT : 0 < T)
    (exceptional : Option Complex)
    (hChoice : IsExceptionalZeroChoice c0 chi exceptional)
    (horiginalX : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt (explicitFormulaIntegrand chi x) rho < 0})
    (horiginalOne : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt (explicitFormulaIntegrand chi 1) rho < 0})
    (hzero : Not ((RectangleBorder (explicitFormulaContourLowerLeft U T)
      (explicitFormulaContourUpperRight c T)) 0)) :
    centeredRegularizedContourResidueSum chi x U c T =
      -(lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex) +
        (-centeredTruncatedCriticalZeroSum chi x T exceptional +
          centeredExceptionalResidueSum chi x exceptional) := by
  unfold centeredRegularizedContourResidueSum
  rw [sumResiduesIn_regularizedContour_eq_decomposed
    hchi hPrimitive x hx c0 U c T hUNonneg hULt hc hT exceptional
    hChoice horiginalX hzero]
  rw [sumResiduesIn_regularizedContour_eq_decomposed
    hchi hPrimitive 1 (by norm_num) c0 U c T hUNonneg hULt hc hT exceptional
    hChoice horiginalOne hzero]
  unfold centeredTruncatedCriticalZeroSum centeredExceptionalResidueSum
  simp
  ring

end BombieriVinogradov.SiegelWalfisz
