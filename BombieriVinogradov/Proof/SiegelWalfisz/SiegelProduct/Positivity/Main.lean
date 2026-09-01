import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Main
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Criterion

/-!
# Strombergsson's positivity lemma near the Siegel pole

This module exposes the uniform source-form positivity criterion with a derived fixed exponent.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
        chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
          DirichletCharacter.mul chi psi ≠ 1 →
          ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
            C * ‖siegelProductResidue chi psi‖ <
              (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
              0 < (siegelProductValue chi psi s).re := by
  obtain ⟨C0, hC0, K, hcoeff⟩ := siegelProduct_coefficient_bound
  let B : ℝ := max 1 (8 * C0)
  have hB : 1 ≤ B := le_max_left _ _
  have hC0B : 8 * C0 ≤ B := le_max_right _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨2 * (Real.exp 2 * B), mul_pos (by norm_num) (mul_pos (Real.exp_pos 2) hBpos),
    4 * K, ?_⟩
  intro N M instN instM instLcm chi psi hchiSquare hpsiSquare hchi hpsi hmul s hsLower hsUpper hsmall
  let Q : ℝ := (N : ℝ) * (M : ℝ)
  let delta : ℝ := 1 - s
  have hdelta : 0 < delta := sub_pos.mpr hsUpper
  have hdeltaUpper : delta ≤ 1 / 8 := by
    dsimp [delta]
    linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_le_mul hN hM (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ N)]
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQ0 : 0 ≤ Q := hQpos.le
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueParts := Complex.le_def.mp hresidue
  have hnormResidue : ‖siegelProductResidue chi psi‖ =
      (siegelProductResidue chi psi).re := by
    have habs := Complex.abs_re_eq_norm.mpr hresidueParts.2.symm
    rw [abs_of_nonneg hresidueParts.1] at habs
    exact habs.symm
  have hsourceSmall :
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
        Q ^ ((4 * K : ℝ) * delta) < delta := by
    have hsmall' : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re <
        delta * Q ^ (-((4 * K : ℝ) * delta)) := by
      simpa [Q, delta, hnormResidue] using hsmall
    have hpowPos : 0 < Q ^ ((4 * K : ℝ) * delta) := Real.rpow_pos_of_pos hQpos _
    calc
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
          Q ^ ((4 * K : ℝ) * delta) <
        (delta * Q ^ (-((4 * K : ℝ) * delta))) *
          Q ^ ((4 * K : ℝ) * delta) :=
        mul_lt_mul_of_pos_right hsmall' hpowPos
      _ = delta := by
        rw [Real.rpow_neg hQ0]
        field_simp
  have hpositive := siegelProduct_pos_of_coefficient_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hC0 hB hC0B hQ hdelta hdeltaUpper
    (fun m => by simpa [Q, mul_assoc] using hcoeff chi psi hchi hpsi hmul m) hsourceSmall
  simpa [delta] using hpositive

end BombieriVinogradov.SiegelWalfisz
