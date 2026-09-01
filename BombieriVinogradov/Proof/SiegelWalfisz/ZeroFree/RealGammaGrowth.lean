import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaCompactRange
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaLargeArgument

/-!
# Uniform real Gamma growth bound

This module combines the compact and large-argument estimates into one
order-one bound valid for every real argument at least one quarter.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem realGamma_le_growth {x : ℝ} (hx : 1 / 4 ≤ x) :
    Real.Gamma x ≤ 4 * (x + 1) ^ (x + 1) := by
  have hbase : 1 ≤ x + 1 := by linarith
  have hexponent : 0 ≤ x + 1 := zero_le_one.trans hbase
  have hpowerOne : 1 ≤ (x + 1) ^ (x + 1) :=
    Real.one_le_rpow hbase hexponent
  by_cases hxTwo : x ≤ 2
  · have hcompact := realGamma_le_four_of_mem_quarter_two hx hxTwo
    nlinarith
  · have hlarge := realGamma_le_rpow_of_two_le (le_of_not_ge hxTwo)
    have hpowerNonneg : 0 ≤ (x + 1) ^ (x + 1) :=
      Real.rpow_nonneg (by linarith) _
    nlinarith

end BombieriVinogradov.SiegelWalfisz
