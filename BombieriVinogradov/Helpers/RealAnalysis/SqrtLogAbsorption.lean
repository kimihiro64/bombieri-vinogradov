import BombieriVinogradov.Helpers.RealAnalysis.SqrtRpow
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Order.Basic

/-!
# Logarithmic losses against square-root-log exponential decay

For each fixed positive rate and real logarithmic exponent, the normalized
loss eventually falls below one. The threshold is not claimed to be uniform
in those earlier parameters.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Square-root-log exponential decay eventually absorbs every real logarithmic power. -/
theorem eventually_log_rpow_mul_exp_sqrt_le_one (b : Real) {a : Real} (ha : 0 < a) :
    Filter.Eventually
      (fun X : Real => (Real.log X) ^ b * Real.exp (-(a * Real.sqrt (Real.log X))) <= 1)
      Filter.atTop := by
  have hLimit := (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * b) a ha).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  have hSmall := (tendsto_order.mp hLimit).2 (1 : Real) zero_lt_one
  refine (hSmall.and (Filter.eventually_ge_atTop (1 : Real))).mono ?_
  intro X h
  have hBound : (Real.sqrt (Real.log X)) ^ (2 * b) *
      Real.exp (-a * Real.sqrt (Real.log X)) < 1 := h.1
  rw [sqrt_rpow_twice (Real.log_nonneg h.2) b, neg_mul] at hBound
  exact hBound.le

end BombieriVinogradov.RealAnalysis
