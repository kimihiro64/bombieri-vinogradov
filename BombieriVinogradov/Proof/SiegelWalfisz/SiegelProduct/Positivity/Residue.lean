import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Main
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.CoefficientBridge
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Positivity of the Siegel-product residue

This module obtains residue positivity as the limit of the nonnegative source coefficients.
-/

set_option autoImplicit false

open scoped ComplexOrder

open Filter
open Topology

namespace BombieriVinogradov.SiegelWalfisz

/-- The common limit of the positive source coefficients is a nonnegative real residue. -/
theorem siegelProductResidue_nonneg {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    0 ≤ siegelProductResidue chi psi := by
  obtain ⟨C, _hC, K, hbound⟩ := siegelProduct_coefficient_bound
  let A : ℝ := C * ((N : ℝ) * (M : ℝ)) ^ K
  have hregular : Tendsto (fun m => siegelRegularCoefficient chi psi m)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg (siegelRegularCoefficient chi psi m))
      (fun m => hbound chi psi hchi hpsi hmul m) ?_
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (show ‖(2 / 3 : ℝ)‖ < 1 by norm_num)
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have hmulZero := hconst.mul hpow
    simpa [A] using hmulZero
  have hsource : Tendsto (fun m => siegelSourceCoefficient chi psi m)
      atTop (𝓝 (siegelProductResidue chi psi)) := by
    have hseq : (fun m => siegelSourceCoefficient chi psi m) =
        fun m => siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
      funext m
      exact siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul m
    rw [hseq]
    simpa using hregular.add_const (siegelProductResidue chi psi)
  exact ge_of_tendsto hsource <| Eventually.of_forall fun m =>
    siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m

end BombieriVinogradov.SiegelWalfisz
