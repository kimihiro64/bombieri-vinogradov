import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ContourResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ResidueDecomposition
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ComplexDifferenceQuotient
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.Rectangle
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered exceptional residual bound

This module extracts the main exceptional-zero term from the centered contour
identity and bounds the remaining reflected difference quotient.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- After the centered retained-zero, origin-multiplicity, and main exceptional
terms are moved to the left, the remaining contour residual has the
quarter-power logarithmic bound. -/
theorem norm_centeredRegularizedContour_exceptionalResidual_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) (x : Nat) (hx : 0 < x)
    (c0 U c T : Real) (hUNonneg : 0 <= U) (hULt : U < 1)
    (hc : 1 <= c) (hT : 0 < T) {beta : Complex}
    (hExceptional : IsExceptionalZero c0 chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1)
    (hBetaLower : (3 / 4 : Real) <= beta.re)
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
    norm (centeredRegularizedContourResidueSum chi x U c T +
        (lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex) +
        centeredTruncatedCriticalZeroSum chi x T (some beta) +
        (((x : Complex) ^ beta - 1) / beta)) <=
      (x : Real) ^ (1 / 4 : Real) * Real.log (x : Real) := by
  have hDistinct : Ne beta (1 - beta) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    simp at hRe
    linarith
  have hDecomp := centeredRegularizedContourResidueSum_eq_decomposed
    hchi hPrimitive x hx c0 U c T hUNonneg hULt hc hT (some beta)
    hExceptional horiginalX horiginalOne hzero
  rw [centeredExceptionalResidueSum_some
    hchi hPrimitive hSquare hx hExceptional hSimple hDistinct] at hDecomp
  have hIdentity :
      centeredRegularizedContourResidueSum chi x U c T +
          (lFunctionOriginMultiplicity chi : Complex) *
            Complex.log (x : Complex) +
          centeredTruncatedCriticalZeroSum chi x T (some beta) +
          (((x : Complex) ^ beta - 1) / beta) =
        -(((x : Complex) ^ (1 - beta) - 1) / (1 - beta)) := by
    rw [hDecomp]
    ring
  rw [hIdentity, norm_neg]
  have hxOneNat : 1 <= x := Nat.succ_le_iff.mpr hx
  have hxOneReal : (1 : Real) <= (x : Real) :=
    Nat.one_le_cast.mpr hxOneNat
  exact norm_reflectedCpowDifferenceQuotient_le hxOneReal
    hExceptional.2.1 hBetaLower hExceptional.2.2.2.1

end BombieriVinogradov.SiegelWalfisz
