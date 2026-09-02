import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Foundations
import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Residue at one Dirichlet L-function zero

This module computes the source integrand's residue at one nonzero point.  At a
zero, `analyticOrderNatAt` is its multiplicity, so the result is exactly the
multiplicity-weighted term used by the truncated explicit formula.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem residue_explicitFormulaIntegrand
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hx : 0 < x) {rho : Complex} (hrho : Ne rho 0) :
    residue (explicitFormulaIntegrand chi x) rho =
      -((analyticOrderNatAt chi.LFunction rho : Nat) : Complex) *
        ((x : Complex) ^ rho / rho) := by
  have hAnalyticAll : forall z : Complex, AnalyticAt Complex chi.LFunction z :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt
  have hLFunctionNeZero : Ne chi.LFunction 0 := by
    intro hzero
    have hone : chi.LFunction 1 = 0 := by
      simpa using congrFun hzero 1
    exact DirichletCharacter.LFunction_apply_one_ne_zero hchi hone
  have hOrderFinite : Ne (analyticOrderAt chi.LFunction rho) (⊤ : ENat) := by
    intro hTop
    exact hLFunctionNeZero
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho hAnalyticAll).mp hTop)
  let n : Int := analyticOrderNatAt chi.LFunction rho
  have hOrder : meromorphicOrderAt chi.LFunction rho = (n : WithTop Int) := by
    rw [(hAnalyticAll rho).meromorphicOrderAt_eq]
    rw [← Nat.cast_analyticOrderNatAt hOrderFinite]
    simp [n]
  have hxComplex : Ne (x : Complex) 0 := by
    exact_mod_cast Nat.ne_of_gt hx
  have hxCpow : ContinuousAt (fun s : Complex => (x : Complex) ^ s) rho :=
    (differentiable_id.const_cpow (Or.inl hxComplex)).continuous.continuousAt
  have hCofactor :
      ContinuousAt (fun s : Complex => -((x : Complex) ^ s / s)) rho :=
    (hxCpow.div continuousAt_id hrho).neg
  have hPrincipal :=
    logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
      (hAnalyticAll rho).meromorphicAt hOrder
  have hResidue :=
    Kadiri.residue_mul_eq_of_sub_principal_isBigO_one hPrincipal hCofactor
  change residue (fun z =>
      logDeriv chi.LFunction z * (-((x : Complex) ^ z / z))) rho = _
  simpa [n] using hResidue

end BombieriVinogradov.SiegelWalfisz
