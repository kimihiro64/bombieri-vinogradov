import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightArcBound

/-!
# Unit Perron error below one

This module normalizes the right-arc estimate.  Its stronger intermediate
bound is one half of `y ^ c`, which immediately implies the source unit bound.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For `0 < y < 1`, the normalized truncated Perron kernel is strictly
smaller than the unit branch `y ^ c`. -/
theorem norm_truncatedPerronKernel_lt_unit_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) < y ^ c := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  have hPowerPos : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  rw [truncatedPerronKernel, VIntegral']
  change norm (a * VIntegral (perronKernelIntegrand y) c (-T) T) < _
  rw [vIntegral_eq_perronRightArcIntegral hy hc hT, norm_mul]
  calc
    norm a * norm (perronRightArcIntegral y c T) <
        norm a * (Real.pi * y ^ c) :=
      mul_lt_mul_of_pos_left
        (norm_perronRightArcIntegral_lt_pi_mul hy hy1 hc hT) hCoeffPos
    _ = y ^ c / 2 := by
      rw [hCoeff]
      field_simp [ne_of_gt Real.pi_pos]
    _ < y ^ c := by linarith

end BombieriVinogradov.SiegelWalfisz
