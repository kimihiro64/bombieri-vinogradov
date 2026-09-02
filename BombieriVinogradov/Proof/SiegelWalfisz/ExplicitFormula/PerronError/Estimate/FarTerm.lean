import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.FarLog
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Far-range Perron summand estimate

This module uses logarithmic separation outside the central dyadic interval to
recover the factor `1 / T` in each far-range summand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A far-range source summand is bounded by `x ^ c / T` times its positive
von Mangoldt L-series term. -/
theorem sourcePerronErrorMajorantTerm_le_farBase
    {x n : Nat} (hx : 0 < x) (hn : 0 < n)
    {c T : Real} (hT : 0 < T)
    (hfar : n <= x / 2 \/ 2 * x <= n) :
    sourcePerronErrorMajorantTerm x c T n <=
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n) := by
  have hLog := half_le_abs_log_ratio_of_far hx hn hfar
  have hLogNonneg : 0 <= abs (Real.log ((x : Real) / (n : Real))) := abs_nonneg _
  have hPiTwo : (2 : Real) <= Real.pi := by
    linarith [Real.pi_gt_three]
  have hPiLog : 1 <= Real.pi *
      abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      (1 : Real) = 2 * (1 / 2) := by norm_num
      _ <= Real.pi * abs (Real.log ((x : Real) / (n : Real))) := by
        exact mul_le_mul hPiTwo hLog (by norm_num) Real.pi_pos.le
  have hDenom : T <= Real.pi * T *
      abs (Real.log ((x : Real) / (n : Real))) := by
    calc
      T = T * 1 := by ring
      _ <= T * (Real.pi *
          abs (Real.log ((x : Real) / (n : Real)))) :=
        mul_le_mul_of_nonneg_left hPiLog hT.le
      _ = Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real))) := by ring
  have hReciprocal :
      1 / (Real.pi * T * abs (Real.log ((x : Real) / (n : Real)))) <=
        1 / T :=
    one_div_le_one_div_of_le hT hDenom
  have hRatioNe : Ne ((x : Real) / (n : Real)) 1 := by
    intro hRatio
    rw [hRatio, Real.log_one, abs_zero] at hLog
    norm_num at hLog
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
      exact min_le_right _ _
    _ <= ArithmeticFunction.vonMangoldt n *
        (((x : Real) / (n : Real)) ^ c * (1 / T)) := by
      gcongr
    _ = ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n) := by
      rw [norm_LSeriesTerm_vonMangoldt_eq,
        Real.div_rpow (Nat.cast_nonneg x) (Nat.cast_nonneg n) c]
      ring

end BombieriVinogradov.SiegelWalfisz
