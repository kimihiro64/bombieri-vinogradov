import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.RegularizedPoleZero
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Upper-strip classification of regularized poles

This module rules out regularized explicit-formula poles on the closed
half-plane with real part at least one.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every nonzero pole of the origin-regularized explicit-formula integrand
has real part strictly less than one. -/
theorem re_lt_one_of_regularizedExplicitFormulaIntegrand_pole
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x)
    {rho : Complex} (hrho : Ne rho 0)
    (hpole : meromorphicOrderAt
      (regularizedExplicitFormulaIntegrand chi x) rho < 0) :
    rho.re < 1 := by
  have hzero : chi.LFunction rho = 0 :=
    LFunction_eq_zero_of_regularizedExplicitFormulaIntegrand_pole
      hchi x hx hrho hpole
  by_contra hnot
  have hone : 1 <= rho.re := le_of_not_gt hnot
  exact (chi.LFunction_ne_zero_of_one_le_re (Or.inl hchi) hone) hzero

end BombieriVinogradov.SiegelWalfisz
