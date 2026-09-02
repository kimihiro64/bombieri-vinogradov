import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightArcGeometry

/-!
# Geometry of the left Perron arc

This module defines the complementary circular arc and proves that its real
part never exceeds `c`.  It also records that its angular length is strictly
less than a full turn.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The circular arc to the left of the vertical line with real part `c`. -/
def perronLeftArc (c T theta : Real) : Complex :=
  circleMap 0 (perronRightArcRadius c T) theta

/-- Every point of the left arc has real part at most `c`. -/
theorem perronLeftArc_re_le
    {c T theta : Real} (hc : 0 < c) (hT : 0 < T)
    (htheta : Set.uIcc (perronRightArcAngle c T)
      (2 * Real.pi - perronRightArcAngle c T) theta) :
    (perronLeftArc c T theta).re <= c := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  have hAngleLt : perronRightArcAngle c T < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hOrdered : perronRightArcAngle c T <=
      2 * Real.pi - perronRightArcAngle c T := by
    linarith [Real.pi_pos]
  have hBounds :
      And (perronRightArcAngle c T <= theta)
        (theta <= 2 * Real.pi - perronRightArcAngle c T) := by
    rw [Set.uIcc_of_le hOrdered] at htheta
    exact htheta
  have hCos : Real.cos theta <= Real.cos (perronRightArcAngle c T) := by
    rcases le_total theta Real.pi with hThetaPi | hPiTheta
    next =>
      exact Real.cos_le_cos_of_nonneg_of_le_pi hAnglePos.le hThetaPi hBounds.1
    next =>
      have hPhiNonneg : 0 <= 2 * Real.pi - theta := by
        linarith [hBounds.2, hAnglePos]
      have hPhiPi : 2 * Real.pi - theta <= Real.pi := by linarith
      have hAnglePhi : perronRightArcAngle c T <=
          2 * Real.pi - theta := by linarith
      have hCosPhi := Real.cos_le_cos_of_nonneg_of_le_pi
        hAnglePos.le hPhiPi hAnglePhi
      simpa [Real.cos_two_pi_sub] using hCosPhi
  have hRadius : 0 <= perronRightArcRadius c T := by
    dsimp [perronRightArcRadius]
    positivity
  have hEndpointRe :
      perronRightArcRadius c T * Real.cos (perronRightArcAngle c T) = c := by
    simpa [perronRightArc, circleMap_zero_re] using
      congrArg Complex.re (perronRightArc_angle (T := T) hc)
  have hMul := mul_le_mul_of_nonneg_left hCos hRadius
  simpa [perronLeftArc, circleMap_zero_re, hEndpointRe] using hMul

/-- The left arc has angular length strictly below `2 * pi`. -/
theorem perronLeftArc_length_lt_two_pi
    {c T : Real} (hc : 0 < c) (hT : 0 < T) :
    (2 * Real.pi - perronRightArcAngle c T) -
        perronRightArcAngle c T < 2 * Real.pi := by
  have hAnglePos : 0 < perronRightArcAngle c T := by
    rw [perronRightArcAngle]
    exact Real.arctan_pos.mpr (div_pos hT hc)
  linarith

end BombieriVinogradov.SiegelWalfisz
