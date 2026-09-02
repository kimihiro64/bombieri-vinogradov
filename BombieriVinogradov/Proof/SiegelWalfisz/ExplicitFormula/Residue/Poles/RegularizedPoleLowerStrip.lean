import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.RegularizedPoleZero
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionZeroLowerStrip

/-!
# Lower-strip classification of regularized poles

This module transfers the primitive L-function zero-strip theorem to nonzero
poles of the regularized explicit-formula integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For a primitive character, every nonzero regularized pole lying to the
right of real part minus one has positive real part. -/
theorem re_pos_of_regularizedExplicitFormulaIntegrand_pole
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) {rho : Complex}
    (hrho : Ne rho 0) (hLower : -1 < rho.re)
    (hpole : meromorphicOrderAt
      (regularizedExplicitFormulaIntegrand chi x) rho < 0) :
    0 < rho.re := by
  apply re_pos_of_LFunction_eq_zero_of_neg_one_lt_re
    hchi hPrimitive hLower hrho
  exact LFunction_eq_zero_of_regularizedExplicitFormulaIntegrand_pole
    hchi x hx hrho hpole

end BombieriVinogradov.SiegelWalfisz
