import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueUpper.Main
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ResidueLower

/-!
# Transfer from the Siegel residue to one L-value

This module uses the logarithmic upper bounds for the two auxiliary factors to
isolate the target character's value at one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelProductResidue_le_log {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    ‖siegelProductResidue chi psi‖ ≤
      characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by
  have hchiBound := norm_LFunction_one_le_log chi hchi
  have hmulBound := norm_LFunction_one_le_log (DirichletCharacter.mul chi psi) hmul
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlogN : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have hfirstUpper : 0 ≤
      (characterLLogBoundConstant * (1 + Real.log N)) * ‖psi.LFunction 1‖ :=
    mul_nonneg (mul_nonneg characterLLogBoundConstant_pos.le hlogN) (norm_nonneg _)
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖chi.LFunction 1‖ * ‖psi.LFunction 1‖ *
        ‖(DirichletCharacter.mul chi psi).LFunction 1‖ ≤
      (characterLLogBoundConstant * (1 + Real.log N)) *
        ‖psi.LFunction 1‖ *
          (characterLLogBoundConstant * (1 + Real.log (N.lcm M))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hchiBound (norm_nonneg _)) hmulBound
        (norm_nonneg _) hfirstUpper
    _ = characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by ring

theorem targetLValue_transfer {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * (characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖) := by
  exact (siegelProductResidue_lower_of_nonpos hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsLower hsUpper hnonpos).trans
      (mul_le_mul_of_nonneg_left (norm_siegelProductResidue_le_log chi psi hchi hmul)
        hpair.1.le)

end BombieriVinogradov.SiegelWalfisz
