import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries

/-!
# Monotonicity of the von Mangoldt norm series

This module proves that increasing the real L-series parameter decreases every
positive von Mangoldt term and hence the complete norm sum.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Each von Mangoldt norm term is antitone in its real exponent. -/
theorem norm_LSeriesTerm_vonMangoldt_antitone
    {c d : Real} (hcd : c <= d) (n : Nat) :
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (d : Complex) n) <=
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) := by
  rw [norm_LSeriesTerm_vonMangoldt_eq,
    norm_LSeriesTerm_vonMangoldt_eq]
  by_cases hn : n = 0
  case pos =>
    subst n
    simp
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnRealPos : 0 < (n : Real) := by exact_mod_cast hnPos
    have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hnPos
    have hPow := Real.rpow_le_rpow_of_exponent_le hnOne hcd
    have hReciprocal : 1 / (n : Real) ^ d <= 1 / (n : Real) ^ c :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnRealPos c) hPow
    calc
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ d =
          ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ d) := by ring
      _ <= ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ c) :=
        mul_le_mul_of_nonneg_left hReciprocal
          ArithmeticFunction.vonMangoldt_nonneg
      _ = ArithmeticFunction.vonMangoldt n / (n : Real) ^ c := by ring

/-- The complete von Mangoldt norm sum is antitone above one. -/
theorem vonMangoldtLSeriesNormSum_antitone
    {c d : Real} (hc : 1 < c) (hcd : c <= d) :
    vonMangoldtLSeriesNormSum d <= vonMangoldtLSeriesNormSum c := by
  have hd : 1 < d := lt_of_lt_of_le hc hcd
  have hSummableD := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (d : Complex)) (by simpa using hd)
  have hSummableC := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  unfold vonMangoldtLSeriesNormSum
  exact hSummableD.norm.tsum_le_tsum
    (norm_LSeriesTerm_vonMangoldt_antitone hcd) hSummableC.norm

end BombieriVinogradov.SiegelWalfisz
