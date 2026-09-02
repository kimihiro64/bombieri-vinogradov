import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedSimpleAtZero
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedSimpleAwayZero
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Simple poles of the regularized integrand

This module combines the separate origin and nonzero pointwise order bounds
into the global simple-pole interface used by rectangle residue calculus.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The double-pole-corrected explicit-formula integrand has at most simple
poles on every set. -/
theorem hasSimplePolesOn_regularizedExplicitFormulaIntegrand
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (U : Set Complex) :
    HasSimplePolesOn (regularizedExplicitFormulaIntegrand chi x) U := by
  intro z _hz
  by_cases hz : z = 0
  case pos =>
    subst z
    exact neg_one_le_meromorphicOrderAt_regularizedExplicitFormulaIntegrand_zero
      hchi x hx
  case neg =>
    exact neg_one_le_meromorphicOrderAt_regularizedExplicitFormulaIntegrand_of_ne_zero
      hchi x hx hz

end BombieriVinogradov.SiegelWalfisz
