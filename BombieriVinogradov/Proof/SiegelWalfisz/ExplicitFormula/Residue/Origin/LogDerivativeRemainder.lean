import BombieriVinogradov.Helpers.ComplexAnalysis.BoundedOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.LFunction
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.LFunctionFiniteOrder
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/-!
# The bounded logarithmic-derivative remainder at the origin

This module proves that subtracting the exact L-function origin principal
part leaves a meromorphic function of nonnegative order at zero.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The origin logarithmic-derivative remainder is meromorphic. -/
theorem meromorphicAt_lFunctionOriginLogDerivativeRemainder
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) :
    MeromorphicAt (lFunctionOriginLogDerivativeRemainder chi) 0 := by
  unfold lFunctionOriginLogDerivativeRemainder
  apply (meromorphic_logDeriv_LFunction hchi 0).sub
  exact (MeromorphicAt.const
    (lFunctionOriginMultiplicity chi : Complex) 0).div (by fun_prop)

/-- After its exact origin principal part is removed, the logarithmic
derivative has nonnegative meromorphic order at zero. -/
theorem meromorphicOrderAt_lFunctionOriginLogDerivativeRemainder_nonneg
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) :
    0 <= meromorphicOrderAt
      (lFunctionOriginLogDerivativeRemainder chi) 0 := by
  have hAnalytic : AnalyticAt Complex chi.LFunction 0 :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt 0
  have hOrderFinite :
      Ne (analyticOrderAt chi.LFunction 0) (Top.top : ENat) := by
    intro hTop
    have hMerOrderTop :
        meromorphicOrderAt chi.LFunction 0 = (Top.top : WithTop Int) := by
      simpa [hTop] using hAnalytic.meromorphicOrderAt_eq
    exact meromorphicOrderAt_LFunction_ne_top hchi 0 hMerOrderTop
  let n : Int := lFunctionOriginMultiplicity chi
  have hOrder :
      meromorphicOrderAt chi.LFunction 0 = (n : WithTop Int) := by
    rw [hAnalytic.meromorphicOrderAt_eq]
    rw [Eq.symm (Nat.cast_analyticOrderNatAt hOrderFinite)]
    simp [n, lFunctionOriginMultiplicity]
  have hBigO :=
    logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
      hAnalytic.meromorphicAt hOrder
  apply BombieriVinogradov.ComplexAnalysis.meromorphicOrderAt_nonneg_of_isBigO_one
      (meromorphicAt_lFunctionOriginLogDerivativeRemainder hchi)
  change
    (logDeriv chi.LFunction - fun s : Complex =>
      (lFunctionOriginMultiplicity chi : Complex) / s) =O[
        nhdsWithin 0 (Compl.compl ({0} : Set Complex))]
      (1 : Complex -> Complex)
  simpa [lFunctionOriginLogDerivativeRemainder, n] using hBigO

end BombieriVinogradov.SiegelWalfisz
