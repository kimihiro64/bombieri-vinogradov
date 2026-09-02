import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.KernelDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.LogDerivativeRemainderValue
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.ScaledRegularizedIdentity
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Residue of the regularized integrand at zero

This module combines the two independently proved finite limits with the
scaled regularized identity to compute the residual origin contribution.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The regularized origin residue is the negative finite logarithmic-derivative
remainder minus the origin multiplicity times log x. -/
theorem residue_regularizedExplicitFormulaIntegrand_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) :
    residue (regularizedExplicitFormulaIntegrand chi x) 0 =
      -lFunctionOriginLogDerivativeRemainderValue chi -
        (lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex) := by
  let punctured := nhdsWithin 0 (Compl.compl ({0} : Set Complex))
  have hxC : Ne (x : Complex) 0 := by
    exact_mod_cast hx.ne'
  have hPowAnalytic :
      AnalyticAt Complex (fun s : Complex => (x : Complex) ^ s) 0 := by
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    fun_prop
  have hPow :
      Filter.Tendsto (fun s : Complex => (x : Complex) ^ s) punctured
        (nhds 1) := by
    simpa [punctured] using
      hPowAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hRemainder :
      Filter.Tendsto (lFunctionOriginLogDerivativeRemainder chi) punctured
        (nhds (lFunctionOriginLogDerivativeRemainderValue chi)) := by
    simpa [punctured] using
      tendsto_lFunctionOriginLogDerivativeRemainder_zero hchi
  have hCompl : Set.compl ({0} : Set Complex) =
      Compl.compl ({0} : Set Complex) := by
    ext z
    rfl
  have hQuotient :
      Filter.Tendsto (originCpowDifferenceQuotient x) punctured
        (nhds (Complex.log (x : Complex))) := by
    simpa [punctured, hCompl] using
      tendsto_originCpowDifferenceQuotient_zero x hx
  have hModel :
      Filter.Tendsto
        (fun s : Complex =>
          -((x : Complex) ^ s * lFunctionOriginLogDerivativeRemainder chi s) -
            (lFunctionOriginMultiplicity chi : Complex) *
              originCpowDifferenceQuotient x s)
        punctured
        (nhds (-lFunctionOriginLogDerivativeRemainderValue chi -
          (lFunctionOriginMultiplicity chi : Complex) *
            Complex.log (x : Complex))) := by
    have hFirst := (hPow.mul hRemainder).neg
    have hSecond :
        Filter.Tendsto
          (fun s : Complex =>
            (lFunctionOriginMultiplicity chi : Complex) *
              originCpowDifferenceQuotient x s)
          punctured
          (nhds ((lFunctionOriginMultiplicity chi : Complex) *
            Complex.log (x : Complex))) :=
      Filter.Tendsto.mul tendsto_const_nhds hQuotient
    simpa using hFirst.sub hSecond
  have hEq : Filter.EventuallyEq punctured
      (fun s : Complex =>
        (s - 0) * regularizedExplicitFormulaIntegrand chi x s)
      (fun s : Complex =>
        -((x : Complex) ^ s * lFunctionOriginLogDerivativeRemainder chi s) -
          (lFunctionOriginMultiplicity chi : Complex) *
            originCpowDifferenceQuotient x s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : Ne s 0 := by
      intro hsEq
      apply hs
      simp [hsEq]
    simpa using
      mul_regularizedExplicitFormulaIntegrand_eq_of_ne_zero chi x hs0
  apply residue_eq_of_tendsto
  exact hModel.congr' hEq.symm

end BombieriVinogradov.SiegelWalfisz
