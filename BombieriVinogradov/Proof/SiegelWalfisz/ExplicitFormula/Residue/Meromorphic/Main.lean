import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.Kernel
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.LFunction

/-!
# Meromorphicity of the explicit-formula integrand

This module combines the independently established logarithmic-derivative and
kernel factors.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The explicit-formula integrand is meromorphic on the complex plane for a
nonprincipal character and positive natural `x`. -/
theorem meromorphic_explicitFormulaIntegrand
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) :
    Meromorphic (explicitFormulaIntegrand chi x) := by
  exact (meromorphic_logDeriv_LFunction hchi).mul
    (meromorphic_explicitFormulaKernel x hx)

/-- The explicit-formula integrand is meromorphic on every set, in particular
on every finite contour rectangle. -/
theorem meromorphicOn_explicitFormulaIntegrand
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (U : Set Complex) :
    MeromorphicOn (explicitFormulaIntegrand chi x) U :=
  (meromorphic_explicitFormulaIntegrand hchi x hx).meromorphicOn

end BombieriVinogradov.SiegelWalfisz
