import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.RegularizedPoleLowerStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.RegularizedPoleUpperStrip

/-!
# Critical-strip classification of regularized poles

This module combines the separate lower- and upper-half-plane classifications
for nonzero poles of the regularized explicit-formula integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For a primitive character, a nonzero regularized pole to the right of real
part minus one lies in the open critical strip. -/
theorem re_mem_Ioo_of_regularizedExplicitFormulaIntegrand_pole
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) {rho : Complex}
    (hrho : Ne rho 0) (hLower : -1 < rho.re)
    (hpole : meromorphicOrderAt
      (regularizedExplicitFormulaIntegrand chi x) rho < 0) :
    Membership.mem (Set.Ioo 0 1) rho.re := by
  apply Set.mem_Ioo.mpr
  exact And.intro
    (re_pos_of_regularizedExplicitFormulaIntegrand_pole
      hchi hPrimitive x hx hrho hLower hpole)
    (re_lt_one_of_regularizedExplicitFormulaIntegrand_pole
      hchi x hx hrho hpole)

end BombieriVinogradov.SiegelWalfisz
