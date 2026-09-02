import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimeNumberTheoremAnd.Rectangle
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered regularized contour residue sum

This module centers the regularized contour residue sum at x equals one.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered contour residue sum is its x-value minus its value at one. -/
def centeredRegularizedContourResidueSum
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (U c T : Real) : Complex :=
  sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
      (Set.inter
        (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
          (explicitFormulaContourUpperRight c T))
        {rho | meromorphicOrderAt
          (regularizedExplicitFormulaIntegrand chi x) rho < 0}) -
    sumResiduesIn (regularizedExplicitFormulaIntegrand chi 1)
      (Set.inter
        (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
          (explicitFormulaContourUpperRight c T))
        {rho | meromorphicOrderAt
          (regularizedExplicitFormulaIntegrand chi 1) rho < 0})

/-- Centering makes the regularized contour residue sum vanish at one. -/
theorem centeredRegularizedContourResidueSum_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (U c T : Real) :
    centeredRegularizedContourResidueSum chi 1 U c T = 0 := by
  simp [centeredRegularizedContourResidueSum]

end BombieriVinogradov.SiegelWalfisz
