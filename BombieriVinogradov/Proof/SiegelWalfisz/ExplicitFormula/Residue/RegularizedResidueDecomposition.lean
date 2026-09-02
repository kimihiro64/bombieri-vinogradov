import BombieriVinogradov.Helpers.ComplexAnalysis.SumResiduesFinset
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.CandidateValueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedCriticalZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedResidueAtZero
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.RegularizedResidueSumCandidates
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Exact regularized residue decomposition

This module combines the contour transfer, finite-set conversion, origin
residue, and retained-zero residue sum while leaving exceptional residues
explicit.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The regularized contour residue sum is the exact sum of the origin
contribution, the negative retained zero sum, and the exceptional residues. -/
theorem sumResiduesIn_regularizedContour_eq_decomposed
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
    (-lFunctionOriginLogDerivativeRemainderValue chi -
        (lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex)) +
      (-truncatedCriticalZeroSum chi x T exceptional +
        Finset.sum (exceptionalZeroValues exceptional)
          (fun rho => residue
            (regularizedExplicitFormulaIntegrand chi x) rho)) := by
  calc
    sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
        (Set.inter
          (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
            (explicitFormulaContourUpperRight c T))
          {rho | meromorphicOrderAt
            (regularizedExplicitFormulaIntegrand chi x) rho < 0}) =
        sumResiduesIn (regularizedExplicitFormulaIntegrand chi x)
          (explicitFormulaResidueCandidateValues chi T exceptional :
            Set Complex) :=
      sumResiduesIn_regularizedContour_eq_candidateValues
        hchi hPrimitive x hx c0 U c T hUNonneg hULt hc hT exceptional
        hChoice horiginal hzero
    _ = Finset.sum (explicitFormulaResidueCandidateValues chi T exceptional)
          (fun rho => residue
            (regularizedExplicitFormulaIntegrand chi x) rho) :=
      BombieriVinogradov.ComplexAnalysis.sumResiduesIn_finset _ _
    _ = residue (regularizedExplicitFormulaIntegrand chi x) 0 +
          (Finset.sum (retainedCriticalZeroValues chi T exceptional)
              (fun rho => residue
                (regularizedExplicitFormulaIntegrand chi x) rho) +
            Finset.sum (exceptionalZeroValues exceptional)
              (fun rho => residue
                (regularizedExplicitFormulaIntegrand chi x) rho)) :=
      sum_explicitFormulaResidueCandidateValues hChoice _
    _ = (-lFunctionOriginLogDerivativeRemainderValue chi -
            (lFunctionOriginMultiplicity chi : Complex) *
              Complex.log (x : Complex)) +
          (-truncatedCriticalZeroSum chi x T exceptional +
            Finset.sum (exceptionalZeroValues exceptional)
              (fun rho => residue
                (regularizedExplicitFormulaIntegrand chi x) rho)) := by
      rw [residue_regularizedExplicitFormulaIntegrand_zero hchi x hx]
      rw [sum_residue_regularizedExplicitFormulaIntegrand_retainedCriticalZeroValues
        hchi hx T exceptional]

end BombieriVinogradov.SiegelWalfisz
