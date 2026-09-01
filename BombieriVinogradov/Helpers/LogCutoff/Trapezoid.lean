import BombieriVinogradov.Helpers.LogCutoff.IntervalBox
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An absolutely integrable logarithmic Fourier cutoff

The normalized convolution below is one on a wide plateau and zero past a
separated endpoint. Its Fourier transform has constant, inverse-frequency,
and inverse-square bounds on three regions, giving an explicit logarithmic
`L1` estimate and an unconditional Fourier inversion formula.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped Convolution FourierTransform Interval

namespace BombieriVinogradov.LogCutoff

/-- A normalized convolution of two interval boxes. Its plateau is wider
than the integer-log range on both sides, so all relevant samples are strict
continuity points. -/
def logTrapezoid (eps L : Real) : Real -> Complex :=
  (eps : Complex)⁻¹ •
    (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
      intervalBox (-2 * eps) (L + eps))

theorem logTrapezoid_integrable (eps L : Real) : Integrable (logTrapezoid eps L) := by
  have h := (intervalBox_integrable 0 eps).integrable_convolution
    (ContinuousLinearMap.mul Complex Complex)
    (intervalBox_integrable (-2 * eps) (L + eps))
  change Integrable (fun x : Real => (eps : Complex)⁻¹ *
    (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
      intervalBox (-2 * eps) (L + eps)) x)
  exact h.const_mul ((eps : Complex)⁻¹)

theorem fourier_logTrapezoid (eps L xi : Real) :
    𝓕 (logTrapezoid eps L) xi =
      (eps : Complex)⁻¹ * 𝓕 (intervalBox 0 eps) xi *
        𝓕 (intervalBox (-2 * eps) (L + eps)) xi := by
  rw [logTrapezoid]
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
      ((eps : Complex)⁻¹ •
        (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
          intervalBox (-2 * eps) (L + eps))) xi = _
  rw [VectorFourier.fourierIntegral_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hconv := Real.fourier_mul_convolution_eq
    (intervalBox_integrable 0 eps)
    (intervalBox_integrable (-2 * eps) (L + eps)) xi
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
      (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
        intervalBox (-2 * eps) (L + eps)) xi = _ at hconv
  rw [hconv]
  ring

theorem norm_fourier_logTrapezoid_le_length (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <= L + 3 * eps := by
  have horder : -2 * eps <= L + eps := by linarith
  have hsmall : ‖𝓕 (intervalBox 0 eps) xi‖ <= eps := by
    simpa using intervalBox_fourier_norm_le_length 0 eps xi heps.le
  have hlarge : ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <= L + 3 * eps := by
    convert intervalBox_fourier_norm_le_length (-2 * eps) (L + eps) xi horder using 1
    ring
  have hinv : ‖(eps : Complex)⁻¹‖ = eps⁻¹ := by
    simp [abs_of_pos heps]
  rw [fourier_logTrapezoid, norm_mul, norm_mul, hinv]
  calc
    eps⁻¹ * ‖𝓕 (intervalBox 0 eps) xi‖ *
        ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <=
      eps⁻¹ * eps * (L + 3 * eps) := by gcongr
    _ = L + 3 * eps := by field_simp [heps.ne']

theorem norm_fourier_logTrapezoid_le_inv (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) (hxi : Ne xi 0) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <= 1 / (Real.pi * |xi|) := by
  have horder : -2 * eps <= L + eps := by linarith
  have hsmall : ‖𝓕 (intervalBox 0 eps) xi‖ <= eps := by
    simpa using intervalBox_fourier_norm_le_length 0 eps xi heps.le
  have hlarge := intervalBox_fourier_norm_le_inv
    (-2 * eps) (L + eps) xi horder hxi
  have hinv : ‖(eps : Complex)⁻¹‖ = eps⁻¹ := by
    simp [abs_of_pos heps]
  rw [fourier_logTrapezoid, norm_mul, norm_mul, hinv]
  calc
    eps⁻¹ * ‖𝓕 (intervalBox 0 eps) xi‖ *
        ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <=
      eps⁻¹ * eps * (1 / (Real.pi * |xi|)) := by gcongr
    _ = 1 / (Real.pi * |xi|) := by field_simp [heps.ne']

theorem norm_fourier_logTrapezoid_le_inv_sq (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) (hxi : Ne xi 0) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <=
      1 / (eps * Real.pi ^ 2 * |xi| ^ 2) := by
  have horder : -2 * eps <= L + eps := by linarith
  have hsmall := intervalBox_fourier_norm_le_inv 0 eps xi heps.le hxi
  have hlarge := intervalBox_fourier_norm_le_inv
    (-2 * eps) (L + eps) xi horder hxi
  have hinv : ‖(eps : Complex)⁻¹‖ = eps⁻¹ := by
    simp [abs_of_pos heps]
  rw [fourier_logTrapezoid, norm_mul, norm_mul, hinv]
  calc
    eps⁻¹ * ‖𝓕 (intervalBox 0 eps) xi‖ *
        ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <=
      eps⁻¹ * (1 / (Real.pi * |xi|)) *
        (1 / (Real.pi * |xi|)) := by gcongr
    _ = 1 / (eps * Real.pi ^ 2 * |xi| ^ 2) := by
      field_simp [heps.ne', Real.pi_ne_zero, abs_ne_zero.mpr hxi]

def centerMajorant (A : Real) : Real -> Real :=
  (Icc 0 A⁻¹).indicator fun _ => A

def middleMajorant (A eps : Real) : Real -> Real :=
  (Ioc A⁻¹ eps⁻¹).indicator fun x => x⁻¹

def tailMajorant (eps : Real) : Real -> Real :=
  (Ioi eps⁻¹).indicator fun x => eps⁻¹ * x ^ (-2 : Real)

def positiveSpectralMajorant (A eps : Real) : Real -> Real :=
  centerMajorant A + middleMajorant A eps + tailMajorant eps

def spectralMajorant (A eps : Real) (x : Real) : Real :=
  positiveSpectralMajorant A eps |x|

theorem centerMajorant_integrable (A : Real) : Integrable (centerMajorant A) := by
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem middleMajorant_integrable (A eps : Real) (hA : 0 < A) :
    Integrable (middleMajorant A eps) := by
  have hcontinuous : ContinuousOn (fun x : Real => x⁻¹) (Icc A⁻¹ eps⁻¹) :=
    continuousOn_inv₀.mono fun x hx => ne_of_gt ((inv_pos.mpr hA).trans_le hx.1)
  exact IntegrableOn.integrable_indicator
    (hcontinuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc

theorem tailMajorant_integrable (eps : Real) (heps : 0 < eps) :
    Integrable (tailMajorant eps) := by
  have htail := integrableOn_Ioi_rpow_of_lt (a := (-2 : Real)) (by norm_num)
    (inv_pos.mpr heps)
  exact IntegrableOn.integrable_indicator (htail.const_mul eps⁻¹) measurableSet_Ioi

theorem positiveSpectralMajorant_integrable (A eps : Real)
    (hA : 0 < A) (heps : 0 < eps) :
    Integrable (positiveSpectralMajorant A eps) := by
  exact ((centerMajorant_integrable A).add (middleMajorant_integrable A eps hA)).add
    (tailMajorant_integrable eps heps)

theorem integral_centerMajorant (A : Real) (hA : 0 < A) :
    ∫ x : Real, centerMajorant A x = 1 := by
  rw [centerMajorant, integral_indicator measurableSet_Icc]
  simp only [integral_const, Measure.real, smul_eq_mul]
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  simp only [sub_zero, ENNReal.toReal_ofReal (inv_nonneg.mpr hA.le)]
  field_simp [hA.ne']

theorem integral_middleMajorant (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) (hepsA : eps <= A) :
    ∫ x : Real, middleMajorant A eps x = Real.log (A / eps) := by
  have hinvle : A⁻¹ <= eps⁻¹ := (inv_le_inv₀ hA heps).2 hepsA
  rw [middleMajorant, integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le hinvle]
  rw [integral_inv_of_pos (inv_pos.mpr hA) (inv_pos.mpr heps)]
  congr 1
  field_simp [hA.ne', heps.ne']

theorem integral_tailMajorant (eps : Real) (heps : 0 < eps) :
    ∫ x : Real, tailMajorant eps x = 1 := by
  rw [tailMajorant, integral_indicator measurableSet_Ioi]
  rw [integral_const_mul]
  rw [integral_Ioi_rpow_of_lt (a := (-2 : Real)) (by norm_num) (inv_pos.mpr heps)]
  norm_num [Real.rpow_neg_one, heps.ne']

theorem integral_positiveSpectralMajorant (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) (hepsA : eps <= A) :
    ∫ x : Real, positiveSpectralMajorant A eps x = 2 + Real.log (A / eps) := by
  have hc := centerMajorant_integrable A
  have hm := middleMajorant_integrable A eps hA
  have ht := tailMajorant_integrable eps heps
  change ∫ x : Real, (centerMajorant A x + middleMajorant A eps x) +
    tailMajorant eps x = _
  calc
    _ = (∫ x : Real, centerMajorant A x + middleMajorant A eps x) +
        ∫ x : Real, tailMajorant eps x := integral_add (hc.add hm) ht
    _ = ((∫ x : Real, centerMajorant A x) +
          ∫ x : Real, middleMajorant A eps x) +
        ∫ x : Real, tailMajorant eps x := by rw [integral_add hc hm]
    _ = 2 + Real.log (A / eps) := by
      rw [integral_centerMajorant A hA,
        integral_middleMajorant A eps hA heps hepsA,
        integral_tailMajorant eps heps]
      ring

theorem positiveSpectralMajorant_eq_zero_of_nonpos (A eps x : Real)
    (hA : 0 < A) (heps : 0 < eps) (hx : x < 0) :
    positiveSpectralMajorant A eps x = 0 := by
  have hAinv : 0 < A⁻¹ := inv_pos.mpr hA
  have hepsinv : 0 < eps⁻¹ := inv_pos.mpr heps
  have hnotcenter : x ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
    (not_le_of_gt hx) hmem.1
  have hnotmiddle : x ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
    (not_lt_of_ge hAinv.le) (hmem.1.trans hx)
  have hnottail : x ∉ Ioi eps⁻¹ := fun hmem =>
    (not_lt_of_ge hepsinv.le) (hmem.trans hx)
  simp [positiveSpectralMajorant, centerMajorant, middleMajorant,
    tailMajorant, hnotcenter, hnotmiddle, hnottail]

theorem spectralMajorant_integrable (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) : Integrable (spectralMajorant A eps) := by
  have hpositive := positiveSpectralMajorant_integrable A eps hA heps
  have hright : IntegrableOn (spectralMajorant A eps) (Ioi (0 : Real)) := by
    refine hpositive.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    rw [spectralMajorant, abs_of_pos (mem_Ioi.mp hx)]
  change IntegrableOn (fun x : Real => positiveSpectralMajorant A eps |x|)
    (Ioi (0 : Real)) at hright
  have hleft : IntegrableOn (spectralMajorant A eps) (Iic (0 : Real)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure Real)]
    let m : MeasurableEmbedding fun x : Real => -x := (Homeomorph.neg Real).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simpa only [Function.comp_def, spectralMajorant, abs_neg, neg_preimage,
      neg_Iic, neg_zero] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright)
  rw [← integrableOn_univ, ← Iic_union_Ioi]
  exact hleft.union hright

theorem integral_spectralMajorant (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) (hepsA : eps <= A) :
    ∫ x : Real, spectralMajorant A eps x =
      4 + 2 * Real.log (A / eps) := by
  change ∫ x : Real, positiveSpectralMajorant A eps |x| = _
  rw [integral_comp_abs]
  have hrestrict :
      ∫ x : Real in Ioi 0, positiveSpectralMajorant A eps x =
        ∫ x : Real, positiveSpectralMajorant A eps x := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [(volume : Measure Real).ae_ne 0] with x hxzero
    by_cases hx : x ∈ Ioi (0 : Real)
    · simp [hx]
    · simp only [Set.indicator_apply, if_neg hx]
      exact (positiveSpectralMajorant_eq_zero_of_nonpos A eps x hA heps
        (lt_of_le_of_ne (not_lt.mp hx) hxzero)).symm
  rw [hrestrict, integral_positiveSpectralMajorant A eps hA heps hepsA]
  ring

theorem norm_fourier_logTrapezoid_le_spectralMajorant (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <= spectralMajorant (L + 3 * eps) eps xi := by
  let A : Real := L + 3 * eps
  have hA : 0 < A := by dsimp [A]; linarith
  have hepsA : eps <= A := by dsimp [A]; linarith
  have hinvle : A⁻¹ <= eps⁻¹ := (inv_le_inv₀ hA heps).2 hepsA
  have hpi : 1 <= Real.pi := by nlinarith [Real.one_le_pi_div_two]
  change ‖𝓕 (logTrapezoid eps L) xi‖ <= spectralMajorant A eps xi
  by_cases hcenter : |xi| <= A⁻¹
  · have hcenterMem : |xi| ∈ Icc (0 : Real) A⁻¹ := ⟨abs_nonneg xi, hcenter⟩
    have hmiddleNot : |xi| ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
      (not_lt_of_ge hcenter) hmem.1
    have htailNot : |xi| ∉ Ioi eps⁻¹ := fun hmem =>
      (not_lt_of_ge (hcenter.trans hinvle)) hmem
    have hbound : ‖𝓕 (logTrapezoid eps L) xi‖ <= A := by
      simpa [A] using norm_fourier_logTrapezoid_le_length eps L xi heps hL
    rw [spectralMajorant]
    simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
      tailMajorant, hcenterMem, hmiddleNot, htailNot] using hbound
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
      have hbound := (norm_fourier_logTrapezoid_le_inv eps L xi heps hL hxi).trans
        hpiBound
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
      have hden : eps * |xi| ^ 2 <= eps * Real.pi ^ 2 * |xi| ^ 2 := by
        calc
          eps * |xi| ^ 2 = (eps * |xi| ^ 2) * 1 := by ring
          _ <= (eps * |xi| ^ 2) * Real.pi ^ 2 :=
            mul_le_mul_of_nonneg_left hpiSq (mul_nonneg heps.le (sq_nonneg _))
          _ = eps * Real.pi ^ 2 * |xi| ^ 2 := by ring
      have hdenPos : 0 < eps * |xi| ^ 2 := mul_pos heps (sq_pos_of_pos hy)
      have hpiBound :
          1 / (eps * Real.pi ^ 2 * |xi| ^ 2) <= 1 / (eps * |xi| ^ 2) := by
        exact one_div_le_one_div_of_le hdenPos hden
      have hrpow : |xi| ^ (-2 : Real) = (|xi| ^ 2)⁻¹ := by
        calc
          |xi| ^ (-2 : Real) = |xi| ^ (-2 : Int) :=
            Real.rpow_neg_natCast |xi| 2
          _ = (|xi| ^ 2)⁻¹ := by norm_num [zpow_neg]
      have halgebra : 1 / (eps * |xi| ^ 2) = eps⁻¹ * |xi| ^ (-2 : Real) := by
        rw [hrpow]
        field_simp [heps.ne', abs_ne_zero.mpr hxi]
      have hbound := (norm_fourier_logTrapezoid_le_inv_sq eps L xi heps hL hxi).trans
        hpiBound
      rw [spectralMajorant]
      simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
        tailMajorant, hcenterNot, hmiddleNot, htailMem, halgebra, mul_comm] using hbound

theorem fourier_logTrapezoid_integrable (eps L : Real)
    (heps : 0 < eps) (hL : 0 <= L) : Integrable (𝓕 (logTrapezoid eps L)) := by
  have hA : 0 < L + 3 * eps := by linarith
  have hmajorant := spectralMajorant_integrable (L + 3 * eps) eps hA heps
  have hcontinuous : Continuous (𝓕 (logTrapezoid eps L)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL Real).continuous₂ (logTrapezoid_integrable eps L)
  exact hmajorant.mono' hcontinuous.aestronglyMeasurable
    (ae_of_all volume fun xi =>
      norm_fourier_logTrapezoid_le_spectralMajorant eps L xi heps hL)

theorem integral_norm_fourier_logTrapezoid_le (eps L : Real)
    (heps : 0 < eps) (hL : 0 <= L) :
    ∫ xi : Real, ‖𝓕 (logTrapezoid eps L) xi‖ <=
      4 + 2 * Real.log ((L + 3 * eps) / eps) := by
  have hA : 0 < L + 3 * eps := by linarith
  have hepsA : eps <= L + 3 * eps := by linarith
  have hfourier := fourier_logTrapezoid_integrable eps L heps hL
  have hmajorant := spectralMajorant_integrable (L + 3 * eps) eps hA heps
  calc
    ∫ xi : Real, ‖𝓕 (logTrapezoid eps L) xi‖ <=
        ∫ xi : Real, spectralMajorant (L + 3 * eps) eps xi := by
      exact integral_mono hfourier.norm hmajorant fun xi =>
        norm_fourier_logTrapezoid_le_spectralMajorant eps L xi heps hL
    _ = 4 + 2 * Real.log ((L + 3 * eps) / eps) :=
      integral_spectralMajorant (L + 3 * eps) eps hA heps hepsA

theorem logTrapezoid_eq_one (eps L x : Real) (heps : 0 < eps)
    (hxlow : -eps <= x) (hxhigh : x <= L + eps) :
    logTrapezoid eps L x = 1 := by
  have hintegrand :
      (fun t : Real => intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = intervalBox 0 eps := by
    funext t
    by_cases ht : t ∈ Icc (0 : Real) eps
    · have hxtlow : -2 * eps <= x - t := by
        rcases ht with ⟨htlow, hthigh⟩
        linarith
      have hxthigh : x - t <= L + eps := by
        rcases ht with ⟨htlow, hthigh⟩
        linarith
      have hxt : x - t ∈ Icc (-2 * eps) (L + eps) := ⟨hxtlow, hxthigh⟩
      simp only [intervalBox, Set.indicator_apply, if_pos ht, if_pos hxt, one_mul]
    · simp only [intervalBox, Set.indicator_apply, if_neg ht, zero_mul]
  change (eps : Complex)⁻¹ *
      (∫ t : Real, intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = 1
  rw [hintegrand, integral_intervalBox 0 eps heps.le]
  norm_num [heps.ne']

theorem logTrapezoid_eq_zero_of_gt (eps L x : Real)
    (hx : L + 2 * eps < x) : logTrapezoid eps L x = 0 := by
  have hintegrand :
      (fun t : Real => intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = 0 := by
    funext t
    by_cases ht : t ∈ Icc (0 : Real) eps
    · have hxt : L + eps < x - t := by
        rcases ht with ⟨htlow, hthigh⟩
        linarith
      have hnot : x - t ∉ Icc (-2 * eps) (L + eps) := fun hmem =>
        (not_le_of_gt hxt) hmem.2
      simp only [intervalBox, Set.indicator_apply, if_pos ht, if_neg hnot, mul_zero]
      rfl
    · simp only [intervalBox, Set.indicator_apply, if_neg ht, zero_mul]
      rfl
  change (eps : Complex)⁻¹ *
      (∫ t : Real, intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = 0
  rw [hintegrand]
  simp

theorem continuousAt_logTrapezoid_of_mem_plateau (eps L x : Real)
    (heps : 0 < eps) (hxlow : -eps < x) (hxhigh : x < L + eps) :
    ContinuousAt (logTrapezoid eps L) x := by
  apply (continuousAt_const : ContinuousAt (fun _ : Real => (1 : Complex)) x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hxlow, hxhigh⟩] with y hy
  exact logTrapezoid_eq_one eps L y heps hy.1.le hy.2.le

theorem continuousAt_logTrapezoid_of_gt (eps L x : Real)
    (hx : L + 2 * eps < x) : ContinuousAt (logTrapezoid eps L) x := by
  apply (continuousAt_const : ContinuousAt (fun _ : Real => (0 : Complex)) x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact logTrapezoid_eq_zero_of_gt eps L y hy

theorem logTrapezoid_fourier_inversion (eps L x : Real)
    (heps : 0 < eps) (hL : 0 <= L)
    (hcontinuous : ContinuousAt (logTrapezoid eps L) x) :
    logTrapezoid eps L x =
      ∫ xi : Real, Real.fourierChar (xi * x) • 𝓕 (logTrapezoid eps L) xi := by
  have hinversion := (logTrapezoid_integrable eps L).fourierInv_fourier_eq
    (fourier_logTrapezoid_integrable eps L heps hL) hcontinuous
  rw [Real.fourierInv_eq] at hinversion
  simpa [mul_comm] using hinversion.symm

end BombieriVinogradov.LogCutoff
