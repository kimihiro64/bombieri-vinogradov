import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Geometry of the right Perron arc

This module defines the circular arc through the two endpoints of the Perron
vertical segment and proves its endpoint and right-half-plane properties.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Radius of the circle through `c - iT` and `c + iT`. -/
def perronRightArcRadius (c T : Real) : Real := Real.sqrt (c ^ 2 + T ^ 2)

/-- Positive endpoint angle of the right circular arc. -/
def perronRightArcAngle (c T : Real) : Real := Real.arctan (T / c)

/-- The circular arc on the right of the vertical line with real part `c`. -/
def perronRightArc (c T theta : Real) : Complex :=
  circleMap 0 (perronRightArcRadius c T) theta

private lemma sqrt_one_add_div_sq
    {c T : Real} (hc : 0 < c) :
    Real.sqrt (1 + (T / c) ^ 2) = perronRightArcRadius c T / c := by
  rw [show 1 + (T / c) ^ 2 = (c ^ 2 + T ^ 2) / c ^ 2 by
    field_simp]
  rw [Real.sqrt_div (by positivity)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hc]
  rfl

/-- The positive endpoint of the right arc is the upper endpoint of the
Perron vertical segment. -/
theorem perronRightArc_angle
    {c T : Real} (hc : 0 < c) :
    perronRightArc c T (perronRightArcAngle c T) =
      (c : Complex) + (T : Complex) * Complex.I := by
  have hRoot := sqrt_one_add_div_sq (T := T) hc
  apply Complex.ext
  next =>
    simp only [perronRightArc, circleMap_zero_re, perronRightArcAngle,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    rw [Real.cos_arctan, hRoot]
    field_simp [ne_of_gt (show 0 < perronRightArcRadius c T by
      dsimp [perronRightArcRadius]
      positivity)]
  next =>
    simp only [perronRightArc, circleMap_zero_im, perronRightArcAngle,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      mul_one, Complex.ofReal_re, Complex.I_re, mul_zero, add_zero]
    rw [Real.sin_arctan, hRoot]
    field_simp [ne_of_gt (show 0 < perronRightArcRadius c T by
      dsimp [perronRightArcRadius]
      positivity)]
    ring

/-- The negative endpoint of the right arc is the lower endpoint of the
Perron vertical segment. -/
theorem perronRightArc_neg_angle
    {c T : Real} (hc : 0 < c) :
    perronRightArc c T (-perronRightArcAngle c T) =
      (c : Complex) - (T : Complex) * Complex.I := by
  have hPlus := perronRightArc_angle (T := T) hc
  apply Complex.ext
  next =>
    simp only [perronRightArc, circleMap_zero_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self]
    rw [Real.cos_neg]
    simpa [perronRightArc, circleMap_zero_re] using congrArg Complex.re hPlus
  next =>
    simp only [perronRightArc, circleMap_zero_im, Complex.sub_im,
      Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
      Complex.ofReal_re, Complex.I_re, mul_zero, zero_sub]
    rw [Real.sin_neg]
    have hIm : perronRightArcRadius c T *
        Real.sin (perronRightArcAngle c T) = T := by
      simpa [perronRightArc, circleMap_zero_im] using congrArg Complex.im hPlus
    nlinarith

/-- Every point of the right arc has real part at least `c`. -/
theorem perronRightArc_re_ge
    {c T theta : Real} (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (-perronRightArcAngle c T)
      (perronRightArcAngle c T) theta) :
    c <= (perronRightArc c T theta).re := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hThetaBounds :
      And (-perronRightArcAngle c T <= theta)
        (theta <= perronRightArcAngle c T) := by
    rw [Set.uIcc_of_le (by linarith :
      -perronRightArcAngle c T <= perronRightArcAngle c T)] at htheta
    change And (-perronRightArcAngle c T <= theta)
      (theta <= perronRightArcAngle c T) at htheta
    exact htheta
  have hAbs : abs theta <= perronRightArcAngle c T :=
    abs_le.mpr hThetaBounds
  have hAnglePi : perronRightArcAngle c T <= Real.pi :=
    (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])
  have hCos :
      Real.cos (perronRightArcAngle c T) <= Real.cos theta := by
    have hCosAbs := Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg theta) hAnglePi hAbs
    simpa using hCosAbs
  have hRadius : 0 <= perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hEndpointRe :
      perronRightArcRadius c T * Real.cos (perronRightArcAngle c T) = c := by
    simpa [perronRightArc, circleMap_zero_re] using
      congrArg Complex.re (perronRightArc_angle (T := T) hc)
  have hMul := mul_le_mul_of_nonneg_left hCos hRadius
  simpa [perronRightArc, circleMap_zero_re, hEndpointRe] using hMul

end BombieriVinogradov.SiegelWalfisz
