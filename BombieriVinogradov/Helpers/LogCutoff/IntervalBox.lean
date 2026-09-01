import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fourier transforms of interval boxes

This module supplies the compactly supported interval functions and the two
complementary Fourier bounds used by the logarithmic cutoff: interval length
near frequency zero and inverse frequency away from zero.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped FourierTransform Interval

namespace BombieriVinogradov.LogCutoff

/-- The complex indicator of a closed real interval. -/
def intervalBox (a b : Real) : Real -> Complex :=
  (Icc a b).indicator fun _ => 1

theorem intervalBox_integrable (a b : Real) : Integrable (intervalBox a b) := by
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem integral_intervalBox (a b : Real) (hab : a <= b) :
    ∫ x : Real, intervalBox a b x = (b - a : Complex) := by
  rw [intervalBox, integral_indicator measurableSet_Icc]
  simp [hab]

theorem intervalBox_fourier_eq_intervalIntegral (a b xi : Real) (hab : a <= b) :
    𝓕 (intervalBox a b) xi =
      ∫ x in a..b, Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * x) := by
  rw [Real.fourier_eq]
  simp only [intervalBox, Circle.smul_def, Real.fourierChar_apply]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc a b
  · simp only [indicator_of_mem hx, smul_eq_mul, mul_one]
    congr 1
    push_cast
    simp
    ring
  · simp [hx]

theorem intervalBox_fourier_of_ne (a b xi : Real) (hab : a <= b) (hxi : Ne xi 0) :
    𝓕 (intervalBox a b) xi =
      (Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * b) -
          Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * a)) /
        (-2 * Real.pi * Complex.I * (xi : Complex)) := by
  rw [intervalBox_fourier_eq_intervalIntegral a b xi hab]
  have hc : Ne (-2 * Real.pi * Complex.I * (xi : Complex)) 0 := by
    norm_num [hxi, Real.pi_ne_zero]
  simpa using
    (integral_exp_mul_complex (a := a) (b := b) hc)

theorem intervalBox_fourier_norm_le_inv (a b xi : Real) (hab : a <= b)
    (hxi : Ne xi 0) :
    ‖𝓕 (intervalBox a b) xi‖ <= 1 / (Real.pi * |xi|) := by
  rw [intervalBox_fourier_of_ne a b xi hab hxi, norm_div]
  have hnum :
      ‖Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * b) -
          Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * a)‖ <= 2 := by
    calc
      _ <= ‖Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * b)‖ +
          ‖Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * a)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        simp [Complex.norm_exp]
        norm_num
  have hden :
      ‖-2 * Real.pi * Complex.I * (xi : Complex)‖ = 2 * Real.pi * |xi| := by
    simp [abs_of_nonneg Real.pi_pos.le, Real.norm_eq_abs]
  rw [hden]
  calc
    _ <= 2 / (2 * Real.pi * |xi|) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / (Real.pi * |xi|) := by
      field_simp

theorem intervalBox_fourier_norm_le_length (a b xi : Real) (hab : a <= b) :
    ‖𝓕 (intervalBox a b) xi‖ <= b - a := by
  calc
    ‖𝓕 (intervalBox a b) xi‖ <= ∫ x : Real, ‖intervalBox a b x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ Real) (intervalBox a b) xi
    _ = b - a := by
      simp only [intervalBox, norm_indicator_eq_indicator_norm, norm_one]
      rw [integral_indicator measurableSet_Icc]
      simp [hab]

end BombieriVinogradov.LogCutoff
