import BombieriVinogradov.Helpers.RealAnalysis.PositiveProductBound
import BombieriVinogradov.Helpers.RealAnalysis.PositiveSelectedHeight
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.ContourWidth
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.ZeroHeightSquare
import Mathlib.Tactic.Positivity

/-!
# Horizontal boundary terms versus the source scale
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem topHorizontalMajorant_le_sourceScale
    {N x : Nat} [NeZero N] {C : Real} (hC : 0 <= C)
    (hN : 3 <= N) (hx : 2 < x)
    {T Tprime : Real} (hT : 2 <= T) (hTx : T <= x)
    (hLower : T <= Tprime) :
    (1 / (2 * Real.pi)) *
        ((C * (zeroHeightLogScale N T) ^ 2) *
          (4 * (x : Real) / abs Tprime) *
            abs (optimizedPerronLine x - (-(1 : Real) / 2))) <=
      (54 / Real.pi) * C *
        ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2) := by
  have hTPos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hHeight : T <= abs Tprime := by
    rw [BombieriVinogradov.RealAnalysis.abs_eq_self_of_two_le_of_le
      hT hLower]
    exact hLower
  exact BombieriVinogradov.RealAnalysis.normalized_horizontal_product_le
    hC (Nat.cast_nonneg x) hTPos hHeight
    (zeroHeightLogScale_sq_le_nine_mul_sourceLog_sq
      hN hx hT hTx)
    (sq_nonneg _)
    (abs_nonneg _)
    (abs_optimizedPerronLine_sub_neg_half_le_three hx)

theorem bottomHorizontalMajorant_le_sourceScale
    {N x : Nat} [NeZero N] {C : Real} (hC : 0 <= C)
    (hN : 3 <= N) (hx : 2 < x)
    {T Tprime : Real} (hT : 2 <= T) (hTx : T <= x)
    (hLower : T <= Tprime) :
    (1 / (2 * Real.pi)) *
        ((C * (zeroHeightLogScale N T) ^ 2) *
          (4 * (x : Real) / abs (-Tprime)) *
            abs ((-(1 : Real) / 2) - optimizedPerronLine x)) <=
      (54 / Real.pi) * C *
        ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2) := by
  have hTPos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hHeight : T <= abs (-Tprime) := by
    rw [BombieriVinogradov.RealAnalysis.abs_neg_eq_self_of_two_le_of_le
      hT hLower]
    exact hLower
  exact BombieriVinogradov.RealAnalysis.normalized_horizontal_product_le
    hC (Nat.cast_nonneg x) hTPos hHeight
    (zeroHeightLogScale_sq_le_nine_mul_sourceLog_sq
      hN hx hT hTx)
    (sq_nonneg _)
    (abs_nonneg _)
    (abs_neg_half_sub_optimizedPerronLine_le_three hx)

end BombieriVinogradov.SiegelWalfisz
