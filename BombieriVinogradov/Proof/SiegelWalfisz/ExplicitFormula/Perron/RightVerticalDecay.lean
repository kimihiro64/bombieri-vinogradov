import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Decay of the right vertical Perron edge

This module bounds the finite right vertical edge and proves that it vanishes
when the rectangle is shifted to positive infinity.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma norm_perron_vertical_integrand_le
    {y R t : Real} (hy : 0 < y) (hR : 0 < R) :
    norm (perronKernelIntegrand y
      ((R : Complex) + (t : Complex) * Complex.I)) <= y ^ R / R := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : R <= norm ((R : Complex) + (t : Complex) * Complex.I) := by
    simpa using Complex.re_le_norm ((R : Complex) + (t : Complex) * Complex.I)
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le R) hR hLower

/-- The unnormalized right vertical edge has a uniform finite-height bound. -/
theorem norm_vIntegral_perron_right_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral (perronKernelIntegrand y) R (-T) T) <=
      2 * T * (y ^ R / R) := by
  rw [VIntegral, norm_smul]
  simp only [Complex.norm_I, one_mul]
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (f := fun t : Real => perronKernelIntegrand y
      ((R : Complex) + (t : Complex) * Complex.I))
    (C := y ^ R / R)
    (fun t _ => norm_perron_vertical_integrand_le hy hR)
  calc
    norm
        (intervalIntegral
          (fun t : Real => perronKernelIntegrand y
            ((R : Complex) + (t : Complex) * Complex.I))
          (-T) T MeasureTheory.volume) <=
        (y ^ R / R) * abs (T - -T) := hIntegral
    _ = 2 * T * (y ^ R / R) := by
      rw [abs_of_nonneg (by linarith)]
      ring

/-- Normalized version of the finite right vertical-edge bound. -/
theorem norm_vIntegral'_perron_right_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral' (perronKernelIntegrand y) R (-T) T) <=
      (T / Real.pi) * (y ^ R / R) := by
  rw [VIntegral', norm_smul]
  calc
    norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        norm (VIntegral (perronKernelIntegrand y) R (-T) T) <=
        norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (2 * T * (y ^ R / R)) := by
      gcongr
      exact norm_vIntegral_perron_right_le hy hR hT
    _ = (T / Real.pi) * (y ^ R / R) := by
      rw [norm_div, norm_one, norm_mul, norm_mul]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      field_simp [ne_of_gt Real.pi_pos]

/-- The normalized right vertical edge vanishes at positive infinity. -/
theorem tendsto_vIntegral'_perron_right_atTop
    {y T : Real} (hy : 0 < y) (hy1 : y < 1) (hT : 0 <= T) :
    Tendsto (fun R : Real =>
      VIntegral' (perronKernelIntegrand y) R (-T) T) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hY : Tendsto (fun R : Real => y ^ R) atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy1
  have hInv : Tendsto (fun R : Real => Inv.inv R) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hMajorant :
      Tendsto (fun R : Real => (T / Real.pi) * (y ^ R / R)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hY.mul hInv).const_mul (T / Real.pi)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hMajorant
  filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
  exact norm_vIntegral'_perron_right_le hy hR hT

end BombieriVinogradov.SiegelWalfisz
