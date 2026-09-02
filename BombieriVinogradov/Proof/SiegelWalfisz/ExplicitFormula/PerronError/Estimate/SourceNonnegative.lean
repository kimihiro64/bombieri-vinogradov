import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions

/-!
# Positivity of the source Perron majorant

This module isolates the pointwise nonnegativity used by range restrictions
and infinite-sum comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every source Perron-error majorant term is nonnegative. -/
theorem sourcePerronErrorMajorantTerm_nonneg
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 0 <= c) (hT : 0 < T)
    (n : Nat) :
    0 <= sourcePerronErrorMajorantTerm x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [sourcePerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      rw [sourcePerronErrorMajorantTerm, if_neg hn, if_pos hRatio]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (div_nonneg hc (mul_nonneg Real.pi_pos.le hT.le))
    case neg =>
      rw [sourcePerronErrorMajorantTerm, if_neg hn, if_neg hRatio]
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
          (le_min zero_le_one hReciprocal))

end BombieriVinogradov.SiegelWalfisz
