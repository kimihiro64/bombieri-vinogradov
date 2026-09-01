import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Bound

/-!
# Uniform decay of the regular Siegel coefficients

This module exposes the source-oriented coefficient estimate obtained by
combining the uniform circle bound with Cauchy's inequalities.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ m : ℕ, ‖siegelRegularCoefficient χ ψ m‖ ≤
            C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  obtain ⟨C, hC, K, hcircle⟩ := siegelPoleSubtracted_circle_bound
  refine ⟨C, hC, K, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul m
  exact norm_siegelRegularCoefficient_le_of_circle_bound χ ψ hχ hψ hmul
    (hcircle χ ψ hχ hψ hmul) m

end BombieriVinogradov.SiegelWalfisz
