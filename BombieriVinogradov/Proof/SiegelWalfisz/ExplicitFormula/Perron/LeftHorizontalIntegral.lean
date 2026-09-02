import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RpowHead

/-!
# Horizontal Perron integrals on a left half-line

This module owns the pointwise horizontal-edge estimate, integrability on a
left half-line, the resulting non-strict norm bound, and convergence of finite
horizontal edges.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz

/-- A horizontal Perron integrand is bounded using the absolute imaginary
part of its denominator. -/
theorem norm_perron_left_horizontal_le
    {y t x : Real} (hy : 0 < y) (ht : 0 < abs t) :
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) <= y ^ x / abs t := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : abs t <=
      norm ((x : Complex) + (t : Complex) * Complex.I) := by
    simpa using Complex.abs_im_le_norm
      ((x : Complex) + (t : Complex) * Complex.I)
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le x) ht hLower

/-- For a base greater than one, the Perron integrand is integrable on every
leftward horizontal half-line away from the real axis. -/
theorem integrableOn_perron_horizontal_Iic
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    IntegrableOn
      (fun x : Real => perronKernelIntegrand y
        ((x : Complex) + (t : Complex) * Complex.I))
      (Iic c) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hDom : IntegrableOn (fun x : Real => y ^ x / abs t) (Iic c) :=
    (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  apply hDom.mono'
  next =>
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Iic
    intro x _
    have hEq :
        (fun u : Real => perronKernelIntegrand y
          ((u : Complex) + (t : Complex) * Complex.I)) =
          fun u : Real =>
            Complex.exp
                ((Real.log y : Complex) *
                  ((u : Complex) + (t : Complex) * Complex.I)) /
              ((u : Complex) + (t : Complex) * Complex.I) := by
      funext u
      exact perronKernelIntegrand_eq_exp hy _
    rw [hEq]
    fun_prop (disch :=
      intro hzero
      have hImag := congrArg Complex.im hzero
      simp at hImag
      exact (ne_of_gt ht) (abs_eq_zero.mpr hImag))
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x _
    exact norm_perron_left_horizontal_le hy ht

/-- The norm of a leftward horizontal Perron integral has the source power
majorant with denominator `abs t`. -/
theorem norm_integral_perron_horizontal_Iic_le
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
      y ^ c / (abs t * abs (Real.log y)) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hDom : IntegrableOn (fun x : Real => y ^ x / abs t) (Iic c) :=
    (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  have hNorm :
      norm
          (integral (volume.restrict (Iic c))
            (fun x : Real => perronKernelIntegrand y
              ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x / abs t) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hDom
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x _
    exact norm_perron_left_horizontal_le hy ht
  calc
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x / abs t) := hNorm
    _ = (1 / abs t) *
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) := by
      rw [show (fun x : Real => y ^ x / abs t) =
          fun x : Real => (1 / abs t) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (abs t * abs (Real.log y)) := by
      rw [integral_rpow_Iic hy1]
      ring

/-- The improper horizontal integral on the ray ending at `c`. -/
def leftHorizontalIntegral (y c t : Real) : Complex :=
  integral (volume.restrict (Iic c))
    (fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))

/-- Finite normalized leftward horizontal edges converge to the normalized
improper horizontal integral. -/
theorem tendsto_hIntegral'_left_atTop
    {y c t : Real} (hy1 : 1 < y) (ht : 0 < abs t) :
    Tendsto
      (fun R : Real => HIntegral' (perronKernelIntegrand y) (-R) c t)
      atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c t)) := by
  have hLimit := intervalIntegral_tendsto_integral_Iic
    (f := fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) c
    (integrableOn_perron_horizontal_Iic hy1 ht)
    tendsto_neg_atTop_atBot
  simpa [HIntegral', HIntegral, leftHorizontalIntegral, smul_eq_mul] using
    hLimit.const_smul (1 / (2 * Real.pi * Complex.I) : Complex)

end BombieriVinogradov.SiegelWalfisz
