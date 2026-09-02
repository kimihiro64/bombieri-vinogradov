import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.NearLog
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Upper central-range Perron summand estimate

This module bounds one source majorant term with `x < n <= 2 * x` by the
integer-distance kernel whose sum is harmonic.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- An upper central-range source summand is controlled by the reciprocal
integer distance from `x`. -/
theorem sourcePerronErrorMajorantTerm_le_upperNear
    {x n : Nat} (hx : 0 < x) (hxn : x < n) (hnTwice : n <= 2 * x)
    {c T : Real} (hc0 : 0 <= c) (hT : 0 < T) :
    sourcePerronErrorMajorantTerm x c T n <=
      8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((n - x : Nat) : Real)) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hn : 0 < n := lt_trans hx hxn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hxnReal : (x : Real) < (n : Real) := by exact_mod_cast hxn
  have hnTwiceReal : (n : Real) <= 2 * (x : Real) := by exact_mod_cast hnTwice
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hRatioOne : (x : Real) / (n : Real) <= 1 := by
    nlinarith [hnReal, hDivMul, hxnReal]
  have hPow : ((x : Real) / (n : Real)) ^ c <= 1 := by
    simpa using Real.rpow_le_rpow hRatioPos.le hRatioOne hc0
  have hLambdaLog : ArithmeticFunction.vonMangoldt n <=
      Real.log (2 * (x : Real)) := by
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnReal hnTwiceReal)
  have hLogTwoXNonneg : 0 <= Real.log (2 * (x : Real)) := by
    apply Real.log_nonneg
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    nlinarith [hxOne]
  have hDistance := cast_sub_div_le_abs_log_ratio_of_gt hx hxn
  have hAbsNonneg : 0 <= abs (Real.log ((x : Real) / (n : Real))) := abs_nonneg _
  have hPiOne : (1 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hPiLog : ((n - x : Nat) : Real) / (n : Real) <=
      Real.pi * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      ((n - x : Nat) : Real) / (n : Real) <=
          abs (Real.log ((x : Real) / (n : Real))) := hDistance
      _ = 1 * abs (Real.log ((x : Real) / (n : Real))) := by ring
      _ <= Real.pi * abs (Real.log ((x : Real) / (n : Real))) :=
        mul_le_mul_of_nonneg_right hPiOne hAbsNonneg
  have hDenom : T * (((n - x : Nat) : Real) / (n : Real)) <=
      Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      T * (((n - x : Nat) : Real) / (n : Real)) <=
          T * (Real.pi * abs (Real.log ((x : Real) / (n : Real)))) :=
        mul_le_mul_of_nonneg_left hPiLog hT.le
      _ = Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by ring
  have hDistPos : 0 < ((n - x : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt hxn
  have hBaseDenomPos : 0 <
      T * (((n - x : Nat) : Real) / (n : Real)) := by
    positivity
  have hReciprocal :
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
        (n : Real) / (T * ((n - x : Nat) : Real)) := by
    calc
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
          1 / (T * (((n - x : Nat) : Real) / (n : Real))) :=
        one_div_le_one_div_of_le hBaseDenomPos hDenom
      _ = (n : Real) / (T * ((n - x : Nat) : Real)) := by
        field_simp [ne_of_gt hnReal, ne_of_gt hT, ne_of_gt hDistPos]
  have hScaled : (n : Real) / (T * ((n - x : Nat) : Real)) <=
      8 * ((x : Real) / (T * ((n - x : Nat) : Real))) := by
    have hnEight : (n : Real) <= 8 * (x : Real) := by
      nlinarith [hnTwiceReal]
    have hUnitNonneg : 0 <= 1 / (T * ((n - x : Nat) : Real)) := by
      positivity
    calc
      (n : Real) / (T * ((n - x : Nat) : Real)) =
          (n : Real) * (1 / (T * ((n - x : Nat) : Real))) := by ring
      _ <= (8 * (x : Real)) *
          (1 / (T * ((n - x : Nat) : Real))) :=
        mul_le_mul_of_nonneg_right hnEight hUnitNonneg
      _ = 8 * ((x : Real) / (T * ((n - x : Nat) : Real))) := by ring
  have hRatioNe : Ne ((x : Real) / (n : Real)) 1 := by
    intro hRatio
    have heq := (div_eq_one_iff_eq (ne_of_gt hnReal)).mp hRatio
    nlinarith
  rw [sourcePerronErrorMajorantTerm, if_neg (Nat.ne_of_gt hn), if_neg hRatioNe]
  calc
    ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          min 1 (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) <=
      ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c *
          (1 / (Real.pi * T *
            abs (Real.log ((x : Real) / (n : Real)))))) := by
      gcongr
      exact min_le_right (1 : Real) _
    _ <= Real.log (2 * (x : Real)) *
        (1 * ((n : Real) / (T * ((n - x : Nat) : Real)))) := by
      exact mul_le_mul hLambdaLog
        (mul_le_mul hPow hReciprocal (by positivity) (by norm_num))
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c) (by positivity))
        hLogTwoXNonneg
    _ <= Real.log (2 * (x : Real)) *
        (8 * ((x : Real) / (T * ((n - x : Nat) : Real)))) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left hScaled hLogTwoXNonneg
    _ = 8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((n - x : Nat) : Real)) := by ring

end BombieriVinogradov.SiegelWalfisz
