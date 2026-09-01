import BombieriVinogradov.Assembly.VaughanMeanValue.FourierBridge
import BombieriVinogradov.Helpers.LogCutoff.Trapezoid
import Mathlib.Tactic

/-!
# One spectral majorant for every bilinear endpoint

The exact cutoff depends on `Y`, but the maximum over `Y <= X` must be taken
before summing over characters. This module dominates all of those Fourier
transforms by one integrable majorant depending only on `X`.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LogCutoff

theorem integerLogGap_eq_log_ratio (Y : Nat) (hY : 1 <= Y) :
    integerLogGap Y = Real.log (((Y + 1 : Nat) : Real) / (Y : Real)) := by
  have hY0 : Ne (Y : Real) 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hY))
  rw [integerLogGap, Real.log_div (by positivity) hY0]

theorem integerLogEpsilon_antitone {Y X : Nat} (hY : 1 <= Y) (hYX : Y <= X) :
    integerLogEpsilon X <= integerLogEpsilon Y := by
  have hX : 1 <= X := hY.trans hYX
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hXpos : 0 < (X : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hratio : (((X + 1 : Nat) : Real) / (X : Real)) <=
      (((Y + 1 : Nat) : Real) / (Y : Real)) := by
    rw [div_le_div_iff₀ hXpos hYpos]
    push_cast
    nlinarith [show (Y : Real) <= (X : Real) by exact_mod_cast hYX]
  have hratioPos : 0 < (((X + 1 : Nat) : Real) / (X : Real)) := by positivity
  have hlog := Real.log_le_log hratioPos hratio
  rw [← integerLogGap_eq_log_ratio X hX,
    ← integerLogGap_eq_log_ratio Y hY] at hlog
  unfold integerLogEpsilon
  linarith

theorem integerLogAmplitude_monotone {Y X : Nat}
    (hY : 1 <= Y) (hYX : Y <= X) :
    Real.log (Y : Real) + 3 * integerLogEpsilon Y <=
      Real.log (X : Real) + 3 * integerLogEpsilon X := by
  have hX : 1 <= X := hY.trans hYX
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hXpos : 0 < (X : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hlogY : Real.log (Y : Real) <= Real.log (X : Real) :=
    Real.strictMonoOn_log.monotoneOn hYpos hXpos (by exact_mod_cast hYX)
  have hlogSucc : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show 0 < ((Y + 1 : Nat) : Real) by positivity)
      (show 0 < ((X + 1 : Nat) : Real) by positivity)
      (by exact_mod_cast Nat.add_le_add_right hYX 1)
  unfold integerLogEpsilon integerLogGap
  linarith

theorem norm_fourier_integerLogCutoff_le_commonSpectralMajorant
    {Y X : Nat} (hY : 1 <= Y) (hYX : Y <= X) (xi : Real) :
    ‖𝓕 (integerLogCutoff Y) xi‖ <=
      spectralMajorant
        (Real.log (X : Real) + 3 * integerLogEpsilon X)
        (integerLogEpsilon X) xi := by
  let A : Real := Real.log (X : Real) + 3 * integerLogEpsilon X
  let eps : Real := integerLogEpsilon X
  have hX : 1 <= X := hY.trans hYX
  have hepsY := integerLogEpsilon_pos Y hY
  have heps : 0 < eps := by simpa [eps] using integerLogEpsilon_pos X hX
  have hLY := log_nat_nonneg Y hY
  have hA : 0 < A := by
    dsimp [A, eps]
    linarith [integerLogEpsilon_pos X hX, log_nat_nonneg X hX]
  have hepsA : eps <= A := by
    dsimp [A, eps]
    linarith [integerLogEpsilon_pos X hX, log_nat_nonneg X hX]
  have hAmplitude : Real.log (Y : Real) + 3 * integerLogEpsilon Y <= A := by
    simpa [A] using integerLogAmplitude_monotone hY hYX
  have hepsOrder : eps <= integerLogEpsilon Y := by
    simpa [eps] using integerLogEpsilon_antitone hY hYX
  have hinvle : A⁻¹ <= eps⁻¹ := (inv_le_inv₀ hA heps).2 hepsA
  have hpi : 1 <= Real.pi := by nlinarith [Real.one_le_pi_div_two]
  change ‖𝓕 (logTrapezoid (integerLogEpsilon Y)
    (Real.log (Y : Real))) xi‖ <= spectralMajorant A eps xi
  by_cases hcenter : |xi| <= A⁻¹
  · have hcenterMem : |xi| ∈ Icc (0 : Real) A⁻¹ := ⟨abs_nonneg xi, hcenter⟩
    have hmiddleNot : |xi| ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
      (not_lt_of_ge hcenter) hmem.1
    have htailNot : |xi| ∉ Ioi eps⁻¹ := fun hmem =>
      (not_lt_of_ge (hcenter.trans hinvle)) hmem
    have hbound := norm_fourier_logTrapezoid_le_length
      (integerLogEpsilon Y) (Real.log (Y : Real)) xi hepsY hLY
    rw [spectralMajorant]
    simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
      tailMajorant, hcenterMem, hmiddleNot, htailNot] using hbound.trans hAmplitude
  · have hAxi : A⁻¹ < |xi| := lt_of_not_ge hcenter
    by_cases hmiddle : |xi| <= eps⁻¹
    · have hmiddleMem : |xi| ∈ Ioc A⁻¹ eps⁻¹ := ⟨hAxi, hmiddle⟩
      have hcenterNot : |xi| ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) hAxi
      have htailNot : |xi| ∉ Ioi eps⁻¹ := fun hmem =>
        (not_lt_of_ge hmiddle) hmem
      have hy : 0 < |xi| := (inv_pos.mpr hA).trans hAxi
      have hxi : Ne xi 0 := abs_pos.mp hy
      have hpiBound : 1 / (Real.pi * |xi|) <= |xi|⁻¹ := by
        have hyMul : |xi| <= Real.pi * |xi| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hy.le
        simpa only [one_div] using one_div_le_one_div_of_le hy hyMul
      have hbound := (norm_fourier_logTrapezoid_le_inv
        (integerLogEpsilon Y) (Real.log (Y : Real)) xi hepsY hLY hxi).trans hpiBound
      rw [spectralMajorant]
      simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
        tailMajorant, hcenterNot, hmiddleMem, htailNot] using hbound
    · have htail : eps⁻¹ < |xi| := lt_of_not_ge hmiddle
      have htailMem : |xi| ∈ Ioi eps⁻¹ := htail
      have hcenterNot : |xi| ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) hAxi
      have hmiddleNot : |xi| ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) htail
      have hy : 0 < |xi| := (inv_pos.mpr heps).trans htail
      have hxi : Ne xi 0 := abs_pos.mp hy
      have hpiSq : 1 <= Real.pi ^ 2 := by nlinarith
      have hden : eps * |xi| ^ 2 <=
          integerLogEpsilon Y * Real.pi ^ 2 * |xi| ^ 2 := by
        calc
          eps * |xi| ^ 2 <= integerLogEpsilon Y * |xi| ^ 2 :=
            mul_le_mul_of_nonneg_right hepsOrder (sq_nonneg _)
          _ = (integerLogEpsilon Y * |xi| ^ 2) * 1 := by ring
          _ <= (integerLogEpsilon Y * |xi| ^ 2) * Real.pi ^ 2 :=
            mul_le_mul_of_nonneg_left hpiSq
              (mul_nonneg hepsY.le (sq_nonneg _))
          _ = integerLogEpsilon Y * Real.pi ^ 2 * |xi| ^ 2 := by ring
      have hdenPos : 0 < eps * |xi| ^ 2 := mul_pos heps (sq_pos_of_pos hy)
      have hpiBound :
          1 / (integerLogEpsilon Y * Real.pi ^ 2 * |xi| ^ 2) <=
            1 / (eps * |xi| ^ 2) := by
        exact one_div_le_one_div_of_le hdenPos hden
      have hrpow : |xi| ^ (-2 : Real) = (|xi| ^ 2)⁻¹ := by
        calc
          |xi| ^ (-2 : Real) = |xi| ^ (-2 : Int) :=
            Real.rpow_neg_natCast |xi| 2
          _ = (|xi| ^ 2)⁻¹ := by norm_num [zpow_neg]
      have halgebra : 1 / (eps * |xi| ^ 2) =
          eps⁻¹ * |xi| ^ (-2 : Real) := by
        rw [hrpow]
        field_simp [heps.ne', abs_ne_zero.mpr hxi]
      have hbound := (norm_fourier_logTrapezoid_le_inv_sq
        (integerLogEpsilon Y) (Real.log (Y : Real)) xi hepsY hLY hxi).trans hpiBound
      rw [spectralMajorant]
      simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
        tailMajorant, hcenterNot, hmiddleNot, htailMem, halgebra, mul_comm] using hbound

theorem spectralMajorant_nonneg (A eps xi : Real)
    (hA : 0 <= A) (heps : 0 <= eps) :
    0 <= spectralMajorant A eps xi := by
  rw [spectralMajorant, positiveSpectralMajorant, centerMajorant,
    middleMajorant, tailMajorant]
  simp only [Pi.add_apply, Set.indicator_apply]
  split_ifs <;> positivity

end BombieriVinogradov.VaughanMeanValue
