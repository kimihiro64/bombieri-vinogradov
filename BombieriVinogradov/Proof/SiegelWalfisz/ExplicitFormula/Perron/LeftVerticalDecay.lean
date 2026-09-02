import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Decay of the left vertical Perron edge

This module bounds the normalized vertical edge at real part `-R` and proves
its decay as `R` tends to positive infinity when the base is greater than one.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

private lemma norm_perron_left_vertical_integrand_le
    {y R t : Real} (hy : 0 < y) (hR : 0 < R) :
    norm (perronKernelIntegrand y
      (((-R : Real) : Complex) + (t : Complex) * Complex.I)) <=
      y ^ (-R) / R := by
  rw [norm_perronKernelIntegrand hy]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hLower : R <=
      norm (((-R : Real) : Complex) + (t : Complex) * Complex.I) := by
    have hAbs := Complex.abs_re_le_norm
      (((-R : Real) : Complex) + (t : Complex) * Complex.I)
    simpa [abs_of_pos hR] using hAbs
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le (-R)) hR hLower

/-- The normalized left vertical edge has a decaying finite-height bound. -/
theorem norm_vIntegral'_perron_left_le
    {y R T : Real} (hy : 0 < y) (hR : 0 < R) (hT : 0 <= T) :
    norm (VIntegral' (perronKernelIntegrand y) (-R) (-T) T) <=
      (T / Real.pi) * (y ^ (-R) / R) := by
  rw [VIntegral', norm_smul]
  have hRaw :
      norm (VIntegral (perronKernelIntegrand y) (-R) (-T) T) <=
        2 * T * (y ^ (-R) / R) := by
    rw [VIntegral, norm_smul]
    simp only [Complex.norm_I, one_mul]
    have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T)
      (f := fun t : Real => perronKernelIntegrand y
        (((-R : Real) : Complex) + (t : Complex) * Complex.I))
      (C := y ^ (-R) / R)
      (fun t _ => norm_perron_left_vertical_integrand_le hy hR)
    calc
      norm
          (intervalIntegral
            (fun t : Real => perronKernelIntegrand y
              (((-R : Real) : Complex) + (t : Complex) * Complex.I))
            (-T) T MeasureTheory.volume) <=
          (y ^ (-R) / R) * abs (T - -T) := hIntegral
      _ = 2 * T * (y ^ (-R) / R) := by
        rw [abs_of_nonneg (by linarith)]
        ring
  calc
    norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        norm (VIntegral (perronKernelIntegrand y) (-R) (-T) T) <=
        norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (2 * T * (y ^ (-R) / R)) := by
      gcongr
    _ = (T / Real.pi) * (y ^ (-R) / R) := by
      rw [norm_div, norm_one, norm_mul, norm_mul]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      field_simp [ne_of_gt Real.pi_pos]

/-- The normalized left vertical edge vanishes as it moves to negative
infinity. -/
theorem tendsto_vIntegral'_perron_left_atTop
    {y T : Real} (hy1 : 1 < y) (hT : 0 <= T) :
    Tendsto (fun R : Real =>
      VIntegral' (perronKernelIntegrand y) (-R) (-T) T) atTop (nhds 0) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hY : Tendsto (fun R : Real => y ^ (-R)) atTop (nhds 0) :=
    (tendsto_rpow_atBot_of_base_gt_one y hy1).comp tendsto_neg_atTop_atBot
  have hInv : Tendsto (fun R : Real => Inv.inv R) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hMajorant :
      Tendsto (fun R : Real => (T / Real.pi) * (y ^ (-R) / R))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hY.mul hInv).const_mul (T / Real.pi)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hMajorant
  filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
  exact norm_vIntegral'_perron_left_le hy hR hT

end BombieriVinogradov.SiegelWalfisz
