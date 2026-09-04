import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ZetaSign
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.PrincipalEulerFactor
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Zero exclusion for principal characters

This module combines the zeta sign immediately left of one with the finite
Euler correction for a principal character. The explicit regular-point
hypothesis excludes the total-function placeholder at the meromorphic pole.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem principal_zeroExclusion_of_zetaInterval
    {epsilon c eta : ℝ} (hepsilon : 0 < epsilon) (hcPos : 0 < c)
    (hcSmall : c ≤ 1 / 16) (hcEta : c ≤ eta)
    (hzeta : ∀ t : ℝ, 1 - eta < t -> t < 1 -> (riemannZeta t).re < 0) :
    ∀ (N : ℕ) [NeZero N] (t : ℝ),
      1 - c * (N : ℝ) ^ (-epsilon) < t -> Ne t 1 ->
        Ne ((1 : DirichletCharacter ℂ N).LFunction t) 0 := by
  intro N _ t ht htNe
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hpowerNonneg : 0 ≤ (N : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg hNpos.le _
  have hpowerLeOne : (N : ℝ) ^ (-epsilon) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNreal (by linarith)
  have hwidthSmall : c * (N : ℝ) ^ (-epsilon) ≤ 1 / 16 := by
    calc
      c * (N : ℝ) ^ (-epsilon) ≤
          (1 / 16 : ℝ) * (N : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_right hcSmall hpowerNonneg
      _ ≤ (1 / 16 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hpowerLeOne (by norm_num)
      _ = 1 / 16 := mul_one _
  have htPos : 0 < t := by linarith
  have hzetaNe : Ne (riemannZeta t) 0 := by
    by_cases htOne : 1 ≤ t
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa using htOne)
    · have htUpper : t < 1 := lt_of_not_ge htOne
      have hwidthEta : c * (N : ℝ) ^ (-epsilon) ≤ eta := by
        calc
          c * (N : ℝ) ^ (-epsilon) ≤ c * 1 :=
            mul_le_mul_of_nonneg_left hpowerLeOne hcPos.le
          _ = c := mul_one _
          _ ≤ eta := hcEta
      have hzetaNeg := hzeta t (by linarith) htUpper
      intro hzero
      rw [hzero] at hzetaNeg
      norm_num at hzetaNeg
  have hproduct := principalEulerProduct_ne_zero_of_pos (N := N) htPos
  have htComplexNe : Ne (t : ℂ) 1 := by exact_mod_cast htNe
  change Ne (DirichletCharacter.LFunctionTrivChar N (t : ℂ)) 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
    (N := N) htComplexNe]
  exact mul_ne_zero hproduct hzetaNe

end BombieriVinogradov.SiegelWalfisz
