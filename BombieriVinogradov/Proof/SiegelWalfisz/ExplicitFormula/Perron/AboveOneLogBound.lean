import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftHorizontalStrict
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftLimitIdentity

/-!
# Logarithmic Perron error above one

This module combines the two strict leftward horizontal-edge estimates and
normalizes them to the logarithmic branch of the scalar Perron error.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The strict logarithmic error term in the above-one Perron estimate. -/
theorem norm_truncatedPerronKernel_sub_one_lt_log_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) <
      y ^ c / (Real.pi * T * abs (Real.log y)) := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  let B : Real := y ^ c / (T * abs (Real.log y))
  have hMinusAbs : 0 < abs (-T) :=
    abs_pos.mpr (neg_ne_zero.mpr hT.ne')
  have hPlusAbs : 0 < abs T := abs_pos.mpr hT.ne'
  have hMinus : norm (leftHorizontalIntegral y c (-T)) < B := by
    simpa [B, leftHorizontalIntegral, abs_of_pos hT] using
      (norm_integral_perron_horizontal_Iic_lt hy1 hc hMinusAbs)
  have hPlus : norm (leftHorizontalIntegral y c T) < B := by
    simpa [B, leftHorizontalIntegral, abs_of_pos hT] using
      (norm_integral_perron_horizontal_Iic_lt hy1 hc hPlusAbs)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  rw [truncatedPerronKernel_sub_one_eq_leftHorizontalIntegrals hy1 hc hT]
  change norm
      (-a * leftHorizontalIntegral y c (-T) +
        a * leftHorizontalIntegral y c T) < _
  calc
    norm
        (-a * leftHorizontalIntegral y c (-T) +
          a * leftHorizontalIntegral y c T) <=
        norm (-a * leftHorizontalIntegral y c (-T)) +
          norm (a * leftHorizontalIntegral y c T) := norm_add_le _ _
    _ = norm a * norm (leftHorizontalIntegral y c (-T)) +
          norm a * norm (leftHorizontalIntegral y c T) := by
      rw [norm_mul, norm_mul, norm_neg]
    _ < norm a * B + norm a * B := by
      exact add_lt_add (mul_lt_mul_of_pos_left hMinus hCoeffPos)
        (mul_lt_mul_of_pos_left hPlus hCoeffPos)
    _ = y ^ c / (Real.pi * T * abs (Real.log y)) := by
      rw [hCoeff]
      dsimp [B]
      field_simp [ne_of_gt Real.pi_pos]
      ring

end BombieriVinogradov.SiegelWalfisz
