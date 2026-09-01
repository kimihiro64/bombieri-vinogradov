import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Main

/-!
# Packaged Siegel-product positivity data

This module packages the absolute constant and exponent from the positivity
lemma behind a short reusable specification.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelPositivityPair (C : ℝ) (D : ℕ) : Prop :=
  0 < C ∧
    ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
      (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
      chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
        DirichletCharacter.mul chi psi ≠ 1 →
        ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
          C * ‖siegelProductResidue chi psi‖ <
            (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
            0 < (siegelProductValue chi psi s).re

theorem exists_siegelPositivityPair :
    ∃ C : ℝ, ∃ D : ℕ, IsSiegelPositivityPair C D := by
  obtain ⟨C, hC, D, hpos⟩ := siegelProduct_pos
  exact ⟨C, D, hC, hpos⟩

end BombieriVinogradov.SiegelWalfisz
