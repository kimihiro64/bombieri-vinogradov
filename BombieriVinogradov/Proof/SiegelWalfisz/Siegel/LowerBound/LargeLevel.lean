import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ExponentControl
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValuePositivity
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueTransfer
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LargeLevelConstants
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LogAbsorption
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.PowerTransfer
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.SeedSelection

/-!
# Siegel's lower bound above the fixed seed level

This module combines the selected seed, the residue estimate, logarithm
absorption, and positive-denominator algebra for target levels above the seed.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound_largeLevel {C epsilon : ℝ} {D N : ℕ}
    {chi : DirichletCharacter ℂ N} {s : ℝ}
    (hpair : IsSiegelPositivityPair C D) (hepsilon : 0 < epsilon)
    (hseed : IsSiegelSeed (siegelLowerEndpoint epsilon D) N chi s) :
    ∀ (M : ℕ) [NeZero M] [NeZero (N.lcm M)]
      (psi : DirichletCharacter ℂ M), N < M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          siegelLargeLevelConstant C epsilon s N * (M : ℝ) ^ (-epsilon) ≤
            (psi.LFunction 1).re := by
  obtain ⟨hN, hchiPrimitive, hchiSquare, hchi, hlowerS,
    hsevenS, hsUpper, hseedNonpos⟩ := hseed
  let _ : NeZero N := ⟨hN.ne'⟩
  intro M _ _ psi hNM hpsiPrimitive hpsiSquare hpsi
  have hM : 0 < M := NeZero.pos M
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne chi psi
    hchiPrimitive hpsiPrimitive (Ne.symm (Nat.ne_of_gt hNM))
  have hnonpos := hseedNonpos M psi hNM hpsiPrimitive hpsiSquare hpsi
  have hraw := targetLValue_transfer hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsevenS hsUpper hnonpos
  have hnorm := norm_quadraticLFunction_one_eq_re psi hpsiSquare hpsi
  rw [hnorm] at hraw
  have hvaluePos := quadraticLFunction_one_re_pos psi hpsiSquare hpsi
  let delta : ℝ := epsilon / 2
  let base : ℝ := (N : ℝ) * (M : ℝ)
  let fixed : ℝ := C * characterLLogBoundConstant ^ 2 * (1 + Real.log N)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbase : 1 ≤ base := by
    dsimp [base]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hM.ne')
  have hfixed : 0 < fixed := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 < 1 + Real.log N := by
      linarith [Real.log_nonneg hNreal]
    dsimp [fixed]
    exact mul_pos (mul_pos hpair.1 (pow_pos characterLLogBoundConstant_pos 2)) hlog
  have hlogBound : 1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * base ^ delta := by
    simpa [delta, base] using one_add_log_lcm_le_rpow_mul hN hM hdelta
  have hscaled : fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re ≤
      fixed * ((1 + delta⁻¹) * base ^ delta) * (psi.LFunction 1).re :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogBound hfixed.le) hvaluePos.le
  have hweighted :
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
        siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
    calc
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
          fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re := by
        simpa [base, fixed, mul_assoc] using hraw
      _ ≤ fixed * ((1 + delta⁻¹) * base ^ delta) *
          (psi.LFunction 1).re := hscaled
      _ = siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
        dsimp [fixed]
        unfold siegelLargeLevelDenominator
        ring
  have hdirect := weighted_rpow_transfer (sub_pos.mpr hsUpper)
    (siegelLargeLevelDenominator_pos hpair.1 hN hdelta) hbase
      (siegel_exponent_control hepsilon D hlowerS) hweighted
  have hbasePower : base ^ (-epsilon) =
      (N : ℝ) ^ (-epsilon) * (M : ℝ) ^ (-epsilon) := by
    dsimp [base]
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hbasePower] at hdirect
  simpa [siegelLargeLevelConstant, delta, mul_assoc] using hdirect

end BombieriVinogradov.SiegelWalfisz
