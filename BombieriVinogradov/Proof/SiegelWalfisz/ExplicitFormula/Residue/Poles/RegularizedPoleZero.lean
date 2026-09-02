import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Nonzero regularized poles are L-function zeros

This module classifies nonzero poles of the regularized explicit-formula
integrand by excluding every regular L-function point analytically.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every nonzero pole of the origin-regularized explicit-formula integrand
is a zero of the Dirichlet L-function. -/
theorem LFunction_eq_zero_of_regularizedExplicitFormulaIntegrand_pole
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x)
    {rho : Complex} (hrho : Ne rho 0)
    (hpole : meromorphicOrderAt
      (regularizedExplicitFormulaIntegrand chi x) rho < 0) :
    chi.LFunction rho = 0 := by
  by_contra hLNe
  have hLAnalytic : AnalyticAt Complex chi.LFunction rho :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt rho
  have hLogAnalytic : AnalyticAt Complex (logDeriv chi.LFunction) rho := by
    unfold logDeriv
    exact hLAnalytic.deriv.div hLAnalytic hLNe
  have hxC : Ne (x : Complex) 0 := by
    exact_mod_cast hx.ne'
  have hPowAnalytic :
      AnalyticAt Complex (fun s : Complex => (x : Complex) ^ s) rho := by
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    fun_prop
  have hKernelAnalytic :
      AnalyticAt Complex (fun s : Complex => -((x : Complex) ^ s / s)) rho :=
    (hPowAnalytic.div (by fun_prop) hrho).neg
  have hOriginalAnalytic :
      AnalyticAt Complex (explicitFormulaIntegrand chi x) rho := by
    unfold explicitFormulaIntegrand
    exact hLogAnalytic.mul hKernelAnalytic
  have hCorrectionAnalytic :
      AnalyticAt Complex (originDoublePoleCorrection chi) rho := by
    unfold originDoublePoleCorrection
    exact (analyticAt_const
      (v := (lFunctionOriginMultiplicity chi : Complex)) (x := rho)).div
        (by fun_prop) (pow_ne_zero 2 hrho)
  have hRegularizedAnalytic :
      AnalyticAt Complex (regularizedExplicitFormulaIntegrand chi x) rho := by
    unfold regularizedExplicitFormulaIntegrand
    exact hOriginalAnalytic.add hCorrectionAnalytic
  exact (not_lt_of_ge hRegularizedAnalytic.meromorphicOrderAt_nonneg) hpole

end BombieriVinogradov.SiegelWalfisz
