import BombieriVinogradov.Helpers.RealAnalysis.NatProductLogBounds
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The imprimitive logarithmic terms fit the primary source scale

The product logarithm dominates both factor logarithms and is at least one.
The height range then makes the primary scale dominate their product and
its level-only linear term, including the endpoint x=2.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem imprimitive_log_terms_le_primaryScale
    {N x : Nat} (hN : 3 <= N) (hx : 2 <= x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    And (Real.log N * Real.log x <=
      (x : Real) / T * (Real.log ((N * x : Nat) : Real)) ^ 2)
      (Real.log N <= (x : Real) / T * (Real.log ((N * x : Nat) : Real)) ^ 2) := by
  let L : Real := Real.log ((N * x : Nat) : Real)
  have hBounds := RealAnalysis.natProductLog_bounds hN hx
  have hLogOne : 1 <= L := hBounds.1
  have hLogNLe : Real.log N <= L := hBounds.2.1
  have hLogxLe : Real.log x <= L := hBounds.2.2
  have hLNonneg : 0 <= L := by linarith
  have hFirst := mul_le_mul_of_nonneg_right hLogNLe (Real.log_natCast_nonneg x)
  have hSecond := mul_le_mul_of_nonneg_left hLogxLe hLNonneg
  have hProductLe : Real.log N * Real.log x <= L ^ 2 := by nlinarith
  have hSquareProduct : 0 <= L * (L - 1) := mul_nonneg hLNonneg (by linarith)
  have hLevelLe : Real.log N <= L ^ 2 := by nlinarith
  have hTPos : 0 < T := by linarith
  have hRatioRaw := div_le_div_of_nonneg_right hTx hTPos.le
  have hRatio : 1 <= (x : Real) / T := by
    simpa [ne_of_gt hTPos] using hRatioRaw
  have hPrimary : L ^ 2 <= (x : Real) / T * L ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hRatio (sq_nonneg L)
  exact And.intro (hProductLe.trans hPrimary) (hLevelLe.trans hPrimary)

end BombieriVinogradov.SiegelWalfisz
