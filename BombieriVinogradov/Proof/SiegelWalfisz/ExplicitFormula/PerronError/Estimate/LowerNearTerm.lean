import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.NearLog
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Lower central-range Perron summand estimate

This module bounds one source majorant term with `x / 2 < n < x` by the
integer-distance kernel whose sum is harmonic.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A lower central-range source summand is controlled by the reciprocal
integer distance from `x`. -/
theorem sourcePerronErrorMajorantTerm_le_lowerNear
    {x n : Nat} (hn : 0 < n) (hnHalf : x / 2 < n) (hnx : n < x)
    {c T : Real} (hc0 : 0 <= c) (hc3 : c <= 3) (hT : 0 < T) :
    sourcePerronErrorMajorantTerm x c T n <=
      8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((x - n : Nat) : Real)) := by
  have hx : 0 < x := lt_trans hn hnx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnxReal : (n : Real) < (x : Real) := by exact_mod_cast hnx
  have hRatioPos : 0 < (x : Real) / (n : Real) := div_pos hxReal hnReal
  have hDivMul : ((x : Real) / (n : Real)) * (n : Real) = (x : Real) := by
    field_simp [ne_of_gt hnReal]
  have hTwice : x <= 2 * n := by omega
  have hTwiceReal : (x : Real) <= 2 * (n : Real) := by exact_mod_cast hTwice
  have hRatioTwo : (x : Real) / (n : Real) <= 2 := by
    nlinarith [hnReal, hDivMul, hTwiceReal]
  have hPow : ((x : Real) / (n : Real)) ^ c <= 8 := by
    calc
      ((x : Real) / (n : Real)) ^ c <= (2 : Real) ^ c :=
        Real.rpow_le_rpow hRatioPos.le hRatioTwo hc0
      _ <= (2 : Real) ^ (3 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hc3
      _ = 8 := by norm_num
  have hnTwoX : n <= 2 * x := by omega
  have hnTwoXReal : (n : Real) <= 2 * (x : Real) := by exact_mod_cast hnTwoX
  have hLambdaLog : ArithmeticFunction.vonMangoldt n <=
      Real.log (2 * (x : Real)) := by
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnReal hnTwoXReal)
  have hLogTwoXNonneg : 0 <= Real.log (2 * (x : Real)) := by
    apply Real.log_nonneg
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    nlinarith [hxOne]
  have hDistance := cast_sub_div_le_abs_log_ratio_of_lt hn hnx
  have hAbsNonneg : 0 <= abs (Real.log ((x : Real) / (n : Real))) := abs_nonneg _
  have hPiOne : (1 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hPiLog : ((x - n : Nat) : Real) / (x : Real) <=
      Real.pi * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      ((x - n : Nat) : Real) / (x : Real) <=
          abs (Real.log ((x : Real) / (n : Real))) := hDistance
      _ = 1 * abs (Real.log ((x : Real) / (n : Real))) := by ring
      _ <= Real.pi * abs (Real.log ((x : Real) / (n : Real))) :=
        mul_le_mul_of_nonneg_right hPiOne hAbsNonneg
  have hDenom : T * (((x - n : Nat) : Real) / (x : Real)) <=
      Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      T * (((x - n : Nat) : Real) / (x : Real)) <=
          T * (Real.pi * abs (Real.log ((x : Real) / (n : Real)))) :=
        mul_le_mul_of_nonneg_left hPiLog hT.le
      _ = Real.pi * T * abs (Real.log ((x : Real) / (n : Real))) := by ring
  have hDistPos : 0 < ((x - n : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt hnx
  have hBaseDenomPos : 0 <
      T * (((x - n : Nat) : Real) / (x : Real)) := by
    positivity
  have hReciprocal :
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
        (x : Real) / (T * ((x - n : Nat) : Real)) := by
    calc
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
          1 / (T * (((x - n : Nat) : Real) / (x : Real))) :=
        one_div_le_one_div_of_le hBaseDenomPos hDenom
      _ = (x : Real) / (T * ((x - n : Nat) : Real)) := by
        field_simp [ne_of_gt hxReal, ne_of_gt hT, ne_of_gt hDistPos]
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
        (8 * ((x : Real) / (T * ((x - n : Nat) : Real)))) := by
      exact mul_le_mul hLambdaLog
        (mul_le_mul hPow hReciprocal (by positivity) (by norm_num))
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c) (by positivity))
        hLogTwoXNonneg
    _ = 8 * (x : Real) * Real.log (2 * (x : Real)) /
        (T * ((x - n : Nat) : Real)) := by ring

end BombieriVinogradov.SiegelWalfisz
