import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightArcIntegral

/-!
# Norm bounds for the right Perron arc

This module bounds the arc integrand pointwise by `y ^ c` when `0 < y < 1`,
then integrates that bound over an arc of angular length strictly below `pi`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The arc derivative cancels the radial denominator in the Perron
integrand's norm. -/
theorem norm_perronRightArc_integrand
    {y c T theta : Real} (hy : 0 < y) (hc : 0 < c) :
    norm ((perronRightArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronRightArc c T theta)) =
      y ^ (perronRightArc c T theta).re := by
  have hRadius : 0 < perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hNorm : norm (perronRightArc c T theta) = perronRightArcRadius c T := by
    rw [perronRightArc, norm_circleMap_zero, abs_of_pos hRadius]
  rw [norm_mul, norm_mul, Complex.norm_I,
    norm_perronKernelIntegrand hy, hNorm]
  field_simp

/-- On the right arc, a base below one is largest at the least real part. -/
theorem norm_perronRightArc_integrand_le
    {y c T theta : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (-perronRightArcAngle c T)
      (perronRightArcAngle c T) theta) :
    norm ((perronRightArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronRightArc c T theta)) <= y ^ c := by
  rw [norm_perronRightArc_integrand hy hc]
  exact Real.rpow_le_rpow_of_exponent_ge hy hy1.le
    (perronRightArc_re_ge hc hT htheta)

/-- The raw arc integral is bounded by the pointwise estimate times its
angular length. -/
theorem norm_perronRightArcIntegral_le
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (perronRightArcIntegral y c T) <=
      y ^ c * abs (perronRightArcAngle c T -
        (-perronRightArcAngle c T)) := by
  rw [perronRightArcIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun theta htheta =>
      norm_perronRightArc_integrand_le hy hy1 hc hT
        (Set.uIoc_subset_uIcc htheta))

/-- The right arc has angular length strictly less than `pi`, yielding the
strict raw integral estimate used by the normalized Perron bound. -/
theorem norm_perronRightArcIntegral_lt_pi_mul
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (perronRightArcIntegral y c T) < Real.pi * y ^ c := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 := by
    exact Real.arctan_lt_pi_div_two (T / c)
  have hLength :
      abs (perronRightArcAngle c T -
        (-perronRightArcAngle c T)) < Real.pi := by
    rw [abs_of_pos (by linarith)]
    linarith
  calc
    norm (perronRightArcIntegral y c T) <=
        y ^ c * abs (perronRightArcAngle c T -
          (-perronRightArcAngle c T)) :=
      norm_perronRightArcIntegral_le hy hy1 hc hT
    _ < y ^ c * Real.pi :=
      mul_lt_mul_of_pos_left hLength (Real.rpow_pos_of_pos hy c)
    _ = Real.pi * y ^ c := by ring

end BombieriVinogradov.SiegelWalfisz
