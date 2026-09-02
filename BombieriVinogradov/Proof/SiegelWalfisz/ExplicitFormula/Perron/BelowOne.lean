import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.BelowOneLogBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.BelowOneUnitBound

/-!
# Truncated Perron estimate below one

This thin consumer combines the independently proved unit and logarithmic
bounds and restores the source step weight, which vanishes when `y < 1`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The two below-one estimates combine into the minimum appearing in the
scalar truncated Perron formula. -/
theorem norm_truncatedPerronKernel_lt_min_bound
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hPowerNonneg : 0 <= y ^ c := (Real.rpow_pos_of_pos hy c).le
  rw [mul_min_of_nonneg 1 (1 / (Real.pi * T * abs (Real.log y)))
    hPowerNonneg]
  apply lt_min
  next =>
    simpa using norm_truncatedPerronKernel_lt_unit_bound hy hy1 hc hT
  next =>
    simpa [div_eq_mul_inv] using
      norm_truncatedPerronKernel_lt_log_bound hy hy1 hc hT

/-- The full source-shaped truncated Perron estimate for `0 < y < 1`. -/
theorem norm_truncatedPerronKernel_sub_stepWeight_lt_of_lt_one
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hWeight : perronStepWeight y = 0 := by
    simp [perronStepWeight, hy1]
  rw [hWeight, Complex.ofReal_zero, sub_zero]
  exact norm_truncatedPerronKernel_lt_min_bound hy hy1 hc hT

end BombieriVinogradov.SiegelWalfisz
