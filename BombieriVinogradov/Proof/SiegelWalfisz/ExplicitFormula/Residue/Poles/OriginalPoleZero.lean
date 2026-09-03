import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.FunProp

/-!
# Nonzero original integrand poles are L-function zeros

This module classifies poles of the unregularized explicit-formula integrand
away from the separate Perron-kernel pole at zero.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_zero_of_explicitFormulaIntegrand_pole
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x)
    {rho : Complex} (hrho : Ne rho 0)
    (hpole : meromorphicOrderAt
      (explicitFormulaIntegrand chi x) rho < 0) :
    chi.LFunction rho = 0 := by
  by_contra hLNe
  have hLAnalytic : AnalyticAt Complex chi.LFunction rho :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt rho
  have hLogAnalytic : AnalyticAt Complex (logDeriv chi.LFunction) rho := by
    unfold logDeriv
    exact hLAnalytic.deriv.div hLAnalytic hLNe
  have hxC : Ne (x : Complex) 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hx)
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
  exact (not_lt_of_ge hOriginalAnalytic.meromorphicOrderAt_nonneg) hpole

end BombieriVinogradov.SiegelWalfisz
