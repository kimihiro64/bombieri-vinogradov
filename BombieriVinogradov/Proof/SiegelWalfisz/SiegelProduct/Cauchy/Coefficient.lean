import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.Main

/-!
# Source-oriented coefficients of the regular Siegel product

This module owns the sign convention translating Taylor coefficients in
`s - 2` into the source's coefficients in powers of `2 - s`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The coefficient of `(2 - s)^m` in the regular pole-subtracted product. -/
noncomputable def siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (siegelPoleSubtracted χ ψ) 2 m

theorem norm_siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ =
      ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖ := by
  rw [siegelRegularCoefficient, norm_mul, norm_pow, norm_neg]
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  rw [hone, one_pow, one_mul]

end BombieriVinogradov.SiegelWalfisz
