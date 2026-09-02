import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.BrokenBoundaryIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ContourResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.VerticalIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Rectangle
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Main
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.Rectangle

/-!
# Centered explicit-formula contour identity

This module subtracts the x equals one rectangle identity from the x identity
on one common finite contour.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered vertical integral is the centered regularized residue sum plus
the centered integral over the other three sides of the rectangle. -/
theorem centeredExplicitFormulaVerticalIntegral_eq_residue_add_boundary
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (U c T : Real)
    (hre : (explicitFormulaContourLowerLeft U T).re <=
      (explicitFormulaContourUpperRight c T).re)
    (him : (explicitFormulaContourLowerLeft U T).im <=
      (explicitFormulaContourUpperRight c T).im)
    (hpolesX : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt (explicitFormulaIntegrand chi x) rho < 0})
    (hpolesOne : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt (explicitFormulaIntegrand chi 1) rho < 0})
    (hzero : Not ((RectangleBorder (explicitFormulaContourLowerLeft U T)
      (explicitFormulaContourUpperRight c T)) 0)) :
    centeredExplicitFormulaVerticalIntegral chi x c T =
      centeredRegularizedContourResidueSum chi x U c T +
        centeredExplicitFormulaBrokenBoundaryIntegral chi x U c T := by
  unfold centeredExplicitFormulaVerticalIntegral
  unfold explicitFormulaVerticalIntegral
  rw [VIntegral'_eq_rectangle_add_brokenBoundary
    (explicitFormulaIntegrand chi x) U c T]
  rw [VIntegral'_eq_rectangle_add_brokenBoundary
    (explicitFormulaIntegrand chi 1) U c T]
  rw [rectangleIntegral'_explicitFormulaIntegrand_eq_sumResiduesIn_regularized
    hchi x hx (explicitFormulaContourLowerLeft U T)
    (explicitFormulaContourUpperRight c T) hre him hpolesX hzero]
  rw [rectangleIntegral'_explicitFormulaIntegrand_eq_sumResiduesIn_regularized
    hchi 1 (by norm_num) (explicitFormulaContourLowerLeft U T)
    (explicitFormulaContourUpperRight c T) hre him hpolesOne hzero]
  unfold centeredRegularizedContourResidueSum
  unfold centeredExplicitFormulaBrokenBoundaryIntegral
  ring

end BombieriVinogradov.SiegelWalfisz
