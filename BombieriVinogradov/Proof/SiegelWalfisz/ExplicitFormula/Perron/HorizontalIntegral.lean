import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RpowTail

/-!
# Horizontal Perron integrals on a right half-line

This module owns the pointwise horizontal-edge estimate, the associated
improper integral, its norm bound, and convergence of finite horizontal edges.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma sqrt_sq_add_sq_le_norm_add_mul_I
    {c t x : Real} (hc : 0 < c) (hcx : c <= x) :
    Real.sqrt (c ^ 2 + t ^ 2) <=
      norm ((x : Complex) + (t : Complex) * Complex.I) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
    Complex.add_im, Complex.mul_im, zero_add]
  apply Real.sqrt_le_sqrt
  nlinarith

/-- A horizontal Perron integrand is dominated by a decaying real power with a
fixed Euclidean denominator. -/
theorem norm_perron_horizontal_le
    {y c t x : Real} (hy : 0 < y) (hc : 0 < c) (hcx : c <= x) :
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) <=
      y ^ x / Real.sqrt (c ^ 2 + t ^ 2) := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : Real.sqrt (c ^ 2 + t ^ 2) <=
      norm ((x : Complex) + (t : Complex) * Complex.I) :=
    sqrt_sq_add_sq_le_norm_add_mul_I hc hcx
  have hD : 0 < Real.sqrt (c ^ 2 + t ^ 2) := by positivity
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le x) hD hLower

/-- The Perron integrand is integrable along every rightward horizontal
half-line when its base lies strictly between zero and one. -/
theorem integrableOn_perron_horizontal_Ioi
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    IntegrableOn
      (fun x : Real => perronKernelIntegrand y
        ((x : Complex) + (t : Complex) * Complex.I))
      (Ioi c) := by
  let D : Real := Real.sqrt (c ^ 2 + t ^ 2)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hDom : IntegrableOn (fun x : Real => y ^ x / D) (Ioi c) :=
    (integrableOn_rpow_Ioi hy hy1 c).div_const D
  apply hDom.mono'
  next =>
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
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
    have hNumerator :
        ContinuousAt
          (fun u : Real =>
            Complex.exp
              ((Real.log y : Complex) *
                ((u : Complex) + (t : Complex) * Complex.I))) x := by
      fun_prop
    have hDenominator :
        ContinuousAt
          (fun u : Real => (u : Complex) + (t : Complex) * Complex.I) x := by
      fun_prop
    have hNe : Ne ((x : Complex) + (t : Complex) * Complex.I) 0 := by
      intro hzero
      have hReal := congrArg Complex.re hzero
      simp at hReal
      change c < x at hx
      linarith
    exact (hNumerator.div hDenominator hNe).continuousWithinAt
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_perron_horizontal_le hy hc hx.le

/-- The norm of a rightward horizontal Perron integral has the exact source
power-tail majorant. -/
theorem norm_integral_perron_horizontal_Ioi_le
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    norm
        (integral (volume.restrict (Ioi c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
      y ^ c /
        (Real.sqrt (c ^ 2 + t ^ 2) * abs (Real.log y)) := by
  let D : Real := Real.sqrt (c ^ 2 + t ^ 2)
  have hDom : IntegrableOn (fun x : Real => y ^ x / D) (Ioi c) :=
    (integrableOn_rpow_Ioi hy hy1 c).div_const D
  have hNorm :
      norm
          (integral (volume.restrict (Ioi c))
            (fun x : Real => perronKernelIntegrand y
              ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x / D) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hDom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_perron_horizontal_le hy hc hx.le
  calc
    norm
        (integral (volume.restrict (Ioi c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x / D) := hNorm
    _ = (1 / D) * integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x) := by
      rw [show (fun x : Real => y ^ x / D) = fun x : Real => (1 / D) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (Real.sqrt (c ^ 2 + t ^ 2) * abs (Real.log y)) := by
      rw [integral_rpow_Ioi hy hy1]
      dsimp [D]
      ring

/-- The improper horizontal integral on the ray starting at `c`. -/
def rightHorizontalIntegral (y c t : Real) : Complex :=
  integral (volume.restrict (Ioi c))
    (fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))

/-- Finite normalized horizontal edges converge to the normalized improper
horizontal integral. -/
theorem tendsto_hIntegral'_right_atTop
    {y c t : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) :
    Tendsto
      (fun R : Real => HIntegral' (perronKernelIntegrand y) c R t)
      atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c t)) := by
  have hLimit := intervalIntegral_tendsto_integral_Ioi
    (f := fun x : Real => perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I)) c
    (integrableOn_perron_horizontal_Ioi (t := t) hy hy1 hc) tendsto_id
  simpa [HIntegral', HIntegral, rightHorizontalIntegral, smul_eq_mul] using
    hLimit.const_smul (1 / (2 * Real.pi * Complex.I) : Complex)

end BombieriVinogradov.SiegelWalfisz
