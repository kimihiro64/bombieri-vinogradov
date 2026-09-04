import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs

/-!
# Absorbing logarithmic powers into a positive power saving

The threshold is existential and may depend on both exponents. The unit
coefficient is asserted only eventually, not at every bounded endpoint.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Every real logarithmic power is eventually below any fixed positive power of X. -/
theorem eventually_log_rpow_le_rpow (b : Real) {delta : Real} (hDelta : 0 < delta) :
    Filter.Eventually (fun X : Real => (Real.log X) ^ b <= X ^ delta) Filter.atTop := by
  have hBound := (_root_.isLittleO_log_rpow_rpow_atTop b hDelta).def
    (show (0 : Real) < 1 from zero_lt_one)
  refine (hBound.and (Filter.eventually_ge_atTop (1 : Real))).mono ?_
  intro X h
  have hX : 0 <= X := zero_le_one.trans h.2
  have hLog : 0 <= (Real.log X) ^ b := Real.rpow_nonneg (Real.log_nonneg h.2) b
  have hPower : 0 <= X ^ delta := Real.rpow_nonneg hX delta
  simpa only [Real.norm_of_nonneg hLog, Real.norm_of_nonneg hPower, one_mul] using h.1

end BombieriVinogradov.RealAnalysis
