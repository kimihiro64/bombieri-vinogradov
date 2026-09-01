import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.LSeries

/-!
# The entire L-function product in Siegel's argument

This module owns the three nonprincipal L-function factors and their value at the zeta pole.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The product of the three entire nonprincipal Dirichlet L-functions in Siegel's argument. -/
noncomputable def siegelLProduct {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  χ.LFunction s * ψ.LFunction s * (DirichletCharacter.mul χ ψ).LFunction s

/-- The residue of the four-factor Siegel product at one. -/
noncomputable def siegelProductResidue {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) : ℂ :=
  χ.LFunction 1 * ψ.LFunction 1 * (DirichletCharacter.mul χ ψ).LFunction 1

theorem siegelLProduct_differentiable {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelLProduct χ ψ) := by
  exact ((DirichletCharacter.differentiable_LFunction hχ).mul
    (DirichletCharacter.differentiable_LFunction hψ)).mul
      (DirichletCharacter.differentiable_LFunction hmul)

theorem siegelLProduct_one {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelLProduct χ ψ 1 = siegelProductResidue χ ψ :=
  rfl

end BombieriVinogradov.SiegelWalfisz
