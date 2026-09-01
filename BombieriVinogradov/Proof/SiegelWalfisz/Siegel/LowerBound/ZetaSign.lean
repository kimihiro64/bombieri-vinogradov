import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Sign of the Riemann zeta function to the left of one

This module derives a left-neighborhood on which the real Riemann zeta
function is negative directly from its residue-one limit.
-/

set_option autoImplicit false

open Filter Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem riemannZeta_im_real (s : ℝ) : (riemannZeta s).im = 0 := by
  have hsym := riemannZeta_conj (s : ℂ)
  have him := congrArg Complex.im hsym
  simp at him
  linarith

theorem exists_riemannZeta_neg_left :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ s : ℝ, 1 - eta < s → s < 1 → (riemannZeta s).re < 0 := by
  have hofReal : Tendsto (fun s : ℝ ↦ (s : ℂ))
      (nhdsWithin 1 (Iio 1)) (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hsne : s ≠ 1 := ne_of_lt (Set.mem_Iio.mp hs)
      change (s : ℂ) ≠ 1
      exact_mod_cast hsne
  have hresidue : Tendsto
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta s).re)
      (nhdsWithin 1 (Iio 1)) (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp
      (riemannZeta_residue_one.comp hofReal) using 1 <;>
        simp [Function.comp_def]
  have heventually : ∀ᶠ s : ℝ in nhdsWithin 1 (Iio 1),
      0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hresidue (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhdsWithin_iff.mp heventually
  refine ⟨eta, heta, ?_⟩
  intro s hsLower hsUpper
  have hdist : dist s 1 < eta := by
    rw [Real.dist_eq]
    rw [abs_of_nonpos (sub_nonpos.mpr hsUpper.le)]
    linarith
  have hproduct : 0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hball ⟨hdist, hsUpper⟩
  have him := riemannZeta_im_real s
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul,
    sub_zero] at hproduct
  nlinarith

end BombieriVinogradov.SiegelWalfisz
