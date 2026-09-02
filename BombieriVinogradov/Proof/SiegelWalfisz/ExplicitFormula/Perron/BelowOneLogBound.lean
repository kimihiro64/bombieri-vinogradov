import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.HorizontalIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightLimitIdentity

/-!
# Logarithmic Perron error below one

This module combines the two rightward horizontal-edge bounds and then uses
the positive real part of the contour to obtain the strict source denominator
`pi * T * abs (log y)`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A slightly stronger non-strict estimate retaining the Euclidean endpoint
distance in the denominator. -/
theorem norm_truncatedPerronKernel_le_sqrt_log_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <=
      y ^ c /
        (Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y)) := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  let B : Real :=
    y ^ c / (Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y))
  have hMinus : norm (rightHorizontalIntegral y c (-T)) <= B := by
    simpa [B, rightHorizontalIntegral] using
      (norm_integral_perron_horizontal_Ioi_le
        (t := -T) hy hy1 hc)
  have hPlus : norm (rightHorizontalIntegral y c T) <= B := by
    simpa [B, rightHorizontalIntegral] using
      (norm_integral_perron_horizontal_Ioi_le
        (t := T) hy hy1 hc)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [truncatedPerronKernel_eq_rightHorizontalIntegrals hy hy1 hc hT]
  change norm
      (a * rightHorizontalIntegral y c (-T) -
        a * rightHorizontalIntegral y c T) <= _
  calc
    norm
        (a * rightHorizontalIntegral y c (-T) -
          a * rightHorizontalIntegral y c T) <=
        norm (a * rightHorizontalIntegral y c (-T)) +
          norm (a * rightHorizontalIntegral y c T) := norm_sub_le _ _
    _ = norm a * norm (rightHorizontalIntegral y c (-T)) +
          norm a * norm (rightHorizontalIntegral y c T) := by
      rw [norm_mul, norm_mul]
    _ <= norm a * B + norm a * B := by
      gcongr
    _ = y ^ c /
          (Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y)) := by
      rw [hCoeff]
      dsimp [B]
      field_simp [ne_of_gt Real.pi_pos]
      ring

/-- The strict logarithmic error term in the below-one Perron estimate. -/
theorem norm_truncatedPerronKernel_lt_log_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <
      y ^ c / (Real.pi * T * abs (Real.log y)) := by
  have hD : T < Real.sqrt (c ^ 2 + T ^ 2) := by
    have hSq : 0 <= c ^ 2 + T ^ 2 := by positivity
    have hSqrtSq := Real.sq_sqrt hSq
    have hSqrtNonneg := Real.sqrt_nonneg (c ^ 2 + T ^ 2)
    nlinarith [sq_pos_of_pos hc]
  have hLogAbs : 0 < abs (Real.log y) :=
    abs_pos.mpr (ne_of_lt (Real.log_neg hy hy1))
  have hNumerator : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  have hSmallDenom : 0 < Real.pi * T * abs (Real.log y) := by positivity
  have hDenomLt :
      Real.pi * T * abs (Real.log y) <
        Real.pi * Real.sqrt (c ^ 2 + T ^ 2) * abs (Real.log y) := by
    nlinarith [Real.pi_pos]
  exact (norm_truncatedPerronKernel_le_sqrt_log_bound hy hy1 hc hT).trans_lt
    (div_lt_div_of_pos_left hNumerator hSmallDenom hDenomLt)

end BombieriVinogradov.SiegelWalfisz
