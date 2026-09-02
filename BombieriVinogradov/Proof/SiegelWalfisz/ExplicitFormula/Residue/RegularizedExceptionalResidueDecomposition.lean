import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.LogDerivativeRemainderValue
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.RegularizedResidueDecomposition
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import PrimeNumberTheoremAnd.Rectangle
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Regularized exceptional residue decomposition

This module specializes the exact contour residue decomposition to a distinct
simple exceptional zero and its reflected partner.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For a distinct simple exceptional zero, the regularized contour residue sum
contains the two exceptional complex-power terms explicitly. -/
theorem sumResiduesIn_regularizedContour_eq_decomposed_exceptional
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) (x : Nat) (hx : 0 < x)
    (c0 U c T : Real) (hUNonneg : 0 <= U) (hULt : U < 1)
    (hc : 1 <= c) (hT : 0 < T) {beta : Complex}
    (hExceptional : IsExceptionalZero c0 chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1)
    (hDistinct : Ne beta (1 - beta))
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
    (-lFunctionOriginLogDerivativeRemainderValue chi -
        (lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex)) +
      (-truncatedCriticalZeroSum chi x T (some beta) +
        (-((x : Complex) ^ beta / beta) +
          -((x : Complex) ^ (1 - beta) / (1 - beta)))) := by
  calc
    sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
        (Set.inter
          (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
            (explicitFormulaContourUpperRight c T))
          {rho | meromorphicOrderAt
            (regularizedExplicitFormulaIntegrand chi x) rho < 0}) =
        (-lFunctionOriginLogDerivativeRemainderValue chi -
            (lFunctionOriginMultiplicity chi : Complex) *
              Complex.log (x : Complex)) +
          (-truncatedCriticalZeroSum chi x T (some beta) +
            Finset.sum (exceptionalZeroValues (some beta))
              (fun rho => residue
                (regularizedExplicitFormulaIntegrand chi x) rho)) :=
      sumResiduesIn_regularizedContour_eq_decomposed
        hchi hPrimitive x hx c0 U c T hUNonneg hULt hc hT (some beta)
        hExceptional horiginal hzero
    _ = (-lFunctionOriginLogDerivativeRemainderValue chi -
            (lFunctionOriginMultiplicity chi : Complex) *
              Complex.log (x : Complex)) +
          (-truncatedCriticalZeroSum chi x T (some beta) +
            (-((x : Complex) ^ beta / beta) +
              -((x : Complex) ^ (1 - beta) / (1 - beta)))) := by
      rw [sum_residue_regularizedExplicitFormulaIntegrand_exceptionalZeroValues_some
        hchi hPrimitive hSquare hx hExceptional hSimple hDistinct]

end BombieriVinogradov.SiegelWalfisz
