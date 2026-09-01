import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.DividedDifference
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.Product
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.ZetaRegularized

/-!
# Pole subtraction for the four-factor Siegel product

This module composes the regular zeta part with an entire divided difference of the L-product.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelPoleSubtracted {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    ℂ → ℂ := fun s ↦
  riemannZeta₀ s * siegelLProduct χ ψ s +
    entireDividedDifference (siegelLProduct χ ψ) 1 s

/-- The pole-subtracted four-factor product is entire when all three character factors are nonprincipal. -/
theorem siegelProduct_sub_pole_entire {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelPoleSubtracted χ ψ) := by
  exact zetaRegularized_differentiable.mul (siegelLProduct_differentiable χ ψ hχ hψ hmul) |>.add
    (entireDividedDifference_differentiable _ _
      (siegelLProduct_differentiable χ ψ hχ hψ hmul))

theorem siegelPoleSubtracted_apply_of_ne {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelPoleSubtracted χ ψ s =
      riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1) := by
  rw [siegelPoleSubtracted, entireDividedDifference_apply_of_ne _ hs,
    siegelLProduct_one, riemannZeta_eq_pole_add_regularized hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

end BombieriVinogradov.SiegelWalfisz
