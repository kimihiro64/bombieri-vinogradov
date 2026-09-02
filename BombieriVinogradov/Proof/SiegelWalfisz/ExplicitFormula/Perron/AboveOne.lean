import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.AboveOneLogBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.AboveOneUnitBound

/-!
# Truncated Perron estimate above one

This thin consumer combines the independently proved unit and logarithmic
bounds and restores the source step weight, which equals one when `y > 1`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The two above-one estimates combine into the minimum appearing in the
scalar truncated Perron formula. -/
theorem norm_truncatedPerronKernel_sub_one_lt_min_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hPowerNonneg : 0 <= y ^ c := (Real.rpow_pos_of_pos hy c).le
  rw [mul_min_of_nonneg 1 (1 / (Real.pi * T * abs (Real.log y)))
    hPowerNonneg]
  apply lt_min
  next =>
    simpa using norm_truncatedPerronKernel_sub_one_lt_unit_bound hy1 hc hT
  next =>
    simpa [div_eq_mul_inv] using
      norm_truncatedPerronKernel_sub_one_lt_log_bound hy1 hc hT

/-- The full source-shaped truncated Perron estimate for `y > 1`. -/
theorem norm_truncatedPerronKernel_sub_stepWeight_lt_of_one_lt
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  have hWeight : perronStepWeight y = 1 := by
    simp [perronStepWeight, not_lt_of_ge hy1.le, ne_of_gt hy1]
  rw [hWeight, Complex.ofReal_one]
  exact norm_truncatedPerronKernel_sub_one_lt_min_bound hy1 hc hT

end BombieriVinogradov.SiegelWalfisz
