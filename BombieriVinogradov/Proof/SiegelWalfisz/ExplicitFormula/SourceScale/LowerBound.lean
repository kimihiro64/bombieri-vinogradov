import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A unit lower bound for the primary source scale

The height range gives x/T at least one, and the source logarithm is at
least one. Their product absorbs absolute centering constants.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem one_le_explicitFormula_primaryScale
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    1 <= (x : Real) / T * (Real.log ((N * x : Nat) : Real)) ^ 2 := by
  let L := Real.log ((N * x : Nat) : Real)
  have hLogOne : 1 <= L := one_le_log_level_mul_argument hN hx
  have hSquare : 0 <= (L - 1) ^ 2 := sq_nonneg (L - 1)
  have hSquareOne : 1 <= L ^ 2 := by nlinarith
  have hTPos : 0 < T := by linarith
  have hRatioRaw : T / T <= (x : Real) / T :=
    div_le_div_of_nonneg_right hTx hTPos.le
  have hRatio : 1 <= (x : Real) / T := by
    simpa [ne_of_gt hTPos] using hRatioRaw
  have hScale : L ^ 2 <= (x : Real) / T * L ^ 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hRatio (sq_nonneg L)
  exact hSquareOne.trans hScale

end BombieriVinogradov.SiegelWalfisz
