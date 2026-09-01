import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Coefficient

/-!
# Entire expansion of the regular Siegel product

This module rewrites the entire Taylor series at two in the source's powers of `2 - s`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The source-oriented regular coefficients sum to the pole-subtracted product everywhere. -/
theorem hasSum_siegelRegularCoefficient {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (s : ℂ) :
    HasSum (fun m : ℕ => siegelRegularCoefficient chi psi m * (2 - s) ^ m)
      (siegelPoleSubtracted chi psi s) := by
  have h := Complex.hasSum_taylorSeries_of_entire
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul) 2 s
  refine HasSum.congr_fun h (fun m => ?_)
  unfold siegelRegularCoefficient BombieriVinogradov.ComplexAnalysis.taylorCoefficient
  simp only [smul_eq_mul]
  have hpow : (s - 2) ^ m = (-1 : ℂ) ^ m * (2 - s) ^ m := by
    rw [show s - 2 = -(2 - s) by ring, neg_pow]
  rw [hpow]
  field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.SiegelWalfisz
