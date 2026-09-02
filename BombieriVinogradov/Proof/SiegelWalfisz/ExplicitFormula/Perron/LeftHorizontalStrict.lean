import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftHorizontalIntegral

/-!
# Strict horizontal Perron bound on a left half-line

The elementary denominator bound is an equality only at real part zero.  This
module turns strictness on a fixed positive-measure interval to the left of
zero into the strict integral estimate used by the source theorem.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

/-- The horizontal Perron integral is strictly smaller than the elementary
power majorant whenever the path stays off the real axis. -/
theorem norm_integral_perron_horizontal_Iic_lt
    {y c t : Real} (hy1 : 1 < y) (hc : 0 < c) (ht : 0 < abs t) :
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <
      y ^ c / (abs t * abs (Real.log y)) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  let mu := volume.restrict (Iic c)
  let f : Real -> Real := fun x =>
    norm (perronKernelIntegrand y
      ((x : Complex) + (t : Complex) * Complex.I))
  let g : Real -> Real := fun x => y ^ x / abs t
  have hf : Integrable f mu := by
    dsimp [f, mu]
    exact (integrableOn_perron_horizontal_Iic hy1 ht).norm
  have hg : Integrable g mu := by
    dsimp [g, mu]
    exact (integrableOn_rpow_Iic hy1 c).div_const (abs t)
  have hfg : Filter.Eventually (fun x => f x <= g x) (ae mu) :=
    Eventually.of_forall fun x => by
      exact norm_perron_left_horizontal_le hy ht
  have hdInt : Integrable (g - f) mu := hg.sub hf
  have hdNonneg : Filter.Eventually (fun x => 0 <= (g - f) x) (ae mu) :=
    hfg.mono fun x hx => by
      simpa only [Pi.sub_apply, sub_nonneg] using hx
  have hSmallSubset : Set.Ioc (-2 : Real) (-1) <= Set.Iic c := by
    intro x hx
    change x <= c
    linarith [hx.2]
  have hSmallSupport :
      Set.Ioc (-2 : Real) (-1) <= Function.support (g - f) := by
    intro x hx
    change Ne ((g - f) x) 0
    apply ne_of_gt
    rw [Pi.sub_apply, sub_pos]
    dsimp [f, g]
    rw [norm_perronKernelIntegrand hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_self, add_zero]
    have hx0 : Ne x 0 := by linarith [hx.2]
    have hDenom : abs t <
        norm ((x : Complex) + (t : Complex) * Complex.I) := by
      have hStrict := (Complex.abs_im_lt_norm).2 (by
        simpa using hx0 :
          Ne (((x : Complex) + (t : Complex) * Complex.I).re) 0)
      simpa using hStrict
    exact div_lt_div_of_pos_left (Real.rpow_pos_of_pos hy x) ht hDenom
  have hSmallMeasure : 0 < mu (Set.Ioc (-2 : Real) (-1)) := by
    dsimp [mu]
    rw [Measure.restrict_apply measurableSet_Ioc]
    rw [Set.inter_eq_left.mpr hSmallSubset]
    norm_num [Real.volume_Ioc]
  have hSupportMeasure : 0 < mu (Function.support (g - f)) :=
    hSmallMeasure.trans_le (measure_mono hSmallSupport)
  have hdPos : 0 < integral mu (g - f) :=
    (integral_pos_iff_support_of_nonneg_ae hdNonneg hdInt).2 hSupportMeasure
  change 0 < integral mu (fun x => g x - f x) at hdPos
  rw [integral_sub hg hf] at hdPos
  have hStrictIntegral : integral mu f < integral mu g := by linarith
  calc
    norm
        (integral (volume.restrict (Iic c))
          (fun x : Real => perronKernelIntegrand y
            ((x : Complex) + (t : Complex) * Complex.I))) <=
        integral mu f := by
      dsimp [mu, f]
      exact norm_integral_le_integral_norm _
    _ < integral mu g := hStrictIntegral
    _ = (1 / abs t) *
        integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) := by
      dsimp [mu, g]
      rw [show (fun x : Real => y ^ x / abs t) =
          fun x : Real => (1 / abs t) * y ^ x by
        funext x
        ring]
      rw [integral_const_mul]
    _ = y ^ c / (abs t * abs (Real.log y)) := by
      rw [integral_rpow_Iic hy1]
      ring

end BombieriVinogradov.SiegelWalfisz
