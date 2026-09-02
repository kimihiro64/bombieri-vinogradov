import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions

/-!
# Logarithmic distance bounds in the near Perron range

This module lower-bounds the logarithmic denominator by the normalized integer
distance from the endpoint, separately below and above `x`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Below `x`, the logarithmic denominator dominates `(x - n) / x`. -/
theorem cast_sub_div_le_abs_log_ratio_of_lt
    {x n : Nat} (hn : 0 < n) (hnx : n < x) :
    ((x - n : Nat) : Real) / (x : Real) <=
      abs (Real.log ((x : Real) / (n : Real))) := by
  have hx : 0 < x := lt_trans hn hnx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnxReal : (n : Real) < (x : Real) := by exact_mod_cast hnx
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hRatioOne : (1 : Real) <= (x : Real) / (n : Real) := by
    nlinarith [hnReal, hDivMul, hnxReal]
  have hLogNonneg : 0 <= Real.log ((x : Real) / (n : Real)) :=
    Real.log_nonneg hRatioOne
  have hInverse : (x : Real) / (n : Real) =
      ((n : Real) / (x : Real)) ^ (-1 : Int) := by
    rw [zpow_neg_one]
    field_simp [ne_of_gt hxReal, ne_of_gt hnReal]
  have hLogInverse : Real.log ((x : Real) / (n : Real)) =
      -Real.log ((n : Real) / (x : Real)) := by
    rw [hInverse, zpow_neg_one, Real.log_inv]
  have hBasic := Real.log_le_sub_one_of_pos (div_pos hnReal hxReal)
  have hCastSub : ((x - n : Nat) : Real) = (x : Real) - (n : Real) := by
    rw [Nat.cast_sub hnx.le]
  have hFraction : ((x : Real) - (n : Real)) / (x : Real) =
      1 - (n : Real) / (x : Real) := by
    field_simp [ne_of_gt hxReal]
  rw [abs_of_nonneg hLogNonneg, hLogInverse, hCastSub, hFraction]
  linarith

/-- Above `x`, the logarithmic denominator dominates `(n - x) / n`. -/
theorem cast_sub_div_le_abs_log_ratio_of_gt
    {x n : Nat} (hx : 0 < x) (hxn : x < n) :
    ((n - x : Nat) : Real) / (n : Real) <=
      abs (Real.log ((x : Real) / (n : Real))) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hn : 0 < n := lt_trans hx hxn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hxnReal : (x : Real) < (n : Real) := by exact_mod_cast hxn
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hRatioOne : (x : Real) / (n : Real) <= 1 := by
    nlinarith [hnReal, hDivMul, hxnReal]
  have hLogNonpos : Real.log ((x : Real) / (n : Real)) <= 0 :=
    Real.log_nonpos hRatioPos.le hRatioOne
  have hBasic := Real.log_le_sub_one_of_pos hRatioPos
  have hCastSub : ((n - x : Nat) : Real) = (n : Real) - (x : Real) := by
    rw [Nat.cast_sub hxn.le]
  have hFraction : ((n : Real) - (x : Real)) / (n : Real) =
      1 - (x : Real) / (n : Real) := by
    field_simp [ne_of_gt hnReal]
  rw [abs_of_nonpos hLogNonpos, hCastSub, hFraction]
  linarith

end BombieriVinogradov.SiegelWalfisz
