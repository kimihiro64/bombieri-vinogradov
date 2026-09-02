import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftArcIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightArcBound

/-!
# Norm bounds for the left Perron arc

This module bounds the left-arc integrand by `y ^ c` for a base greater than
one, then uses the fact that the complementary arc has length below a full
turn.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- On the left arc, a base greater than one is largest at the greatest real
part. -/
theorem norm_perronLeftArc_integrand_le
    {y c T theta : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (perronRightArcAngle c T)
      (2 * Real.pi - perronRightArcAngle c T) theta) :
    norm ((perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)) <= y ^ c := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [show norm ((perronLeftArc c T theta * Complex.I) *
      perronKernelIntegrand y (perronLeftArc c T theta)) =
      y ^ (perronLeftArc c T theta).re by
    simpa [perronLeftArc, perronRightArc] using
      (norm_perronRightArc_integrand (T := T) (theta := theta) hy hc)]
  exact Real.rpow_le_rpow_of_exponent_le hy1.le
    (perronLeftArc_re_le hc hT htheta)

/-- The raw left-arc integral is bounded by the pointwise estimate times its
angular length. -/
theorem norm_perronLeftArcIntegral_le
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (perronLeftArcIntegral y c T) <=
      y ^ c * abs ((2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T) := by
  rw [perronLeftArcIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun theta htheta =>
      norm_perronLeftArc_integrand_le hy1 hc hT
        (Set.uIoc_subset_uIcc htheta))

/-- The raw left-arc integral is strictly below a full-turn majorant. -/
theorem norm_perronLeftArcIntegral_lt_two_pi_mul
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (perronLeftArcIntegral y c T) < 2 * Real.pi * y ^ c := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hLengthPos : 0 <
      (2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T := by
    linarith [Real.pi_pos]
  have hLength := perronLeftArc_length_lt_two_pi hc hT
  calc
    norm (perronLeftArcIntegral y c T) <=
        y ^ c * abs ((2 * Real.pi - perronRightArcAngle c T) -
          perronRightArcAngle c T) :=
      norm_perronLeftArcIntegral_le hy1 hc hT
    _ = y ^ c * ((2 * Real.pi - perronRightArcAngle c T) -
          perronRightArcAngle c T) := by
      rw [abs_of_pos hLengthPos]
    _ < y ^ c * (2 * Real.pi) :=
      mul_lt_mul_of_pos_left hLength (Real.rpow_pos_of_pos hy c)
    _ = 2 * Real.pi * y ^ c := by ring

end BombieriVinogradov.SiegelWalfisz
