import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.FarTerm
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.SourceNonnegative
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries

/-!
# Far-range Perron sum

This module restricts the source majorant to the far dyadic range and sums the
pointwise `1 / T` estimate against the von Mangoldt L-series.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The source Perron majorant outside the central dyadic interval. -/
def farSourcePerronErrorTerm
    (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n <= x / 2 \/ 2 * x <= n then
    sourcePerronErrorMajorantTerm x c T n
  else 0

/-- The restricted far-range term is nonnegative. -/
theorem farSourcePerronErrorTerm_nonneg
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 0 <= c) (hT : 0 < T)
    (n : Nat) :
    0 <= farSourcePerronErrorTerm x c T n := by
  unfold farSourcePerronErrorTerm
  split
  case isTrue =>
    exact sourcePerronErrorMajorantTerm_nonneg hx hc hT n
  case isFalse =>
    exact le_refl 0

/-- The restricted far-range term is bounded by the summable L-series term. -/
theorem farSourcePerronErrorTerm_le_base
    {x : Nat} (hx : 0 < x) {c T : Real} (hT : 0 < T) (n : Nat) :
    farSourcePerronErrorTerm x c T n <=
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [farSourcePerronErrorTerm, sourcePerronErrorMajorantTerm,
      LSeries.term_def]
  case neg =>
    by_cases hfar : n <= x / 2 \/ 2 * x <= n
    case pos =>
      rw [farSourcePerronErrorTerm, if_pos hfar]
      exact sourcePerronErrorMajorantTerm_le_farBase hx
        (Nat.pos_of_ne_zero hn) hT hfar
    case neg =>
      rw [farSourcePerronErrorTerm, if_neg hfar]
      positivity

/-- The far-range restriction is summable for `c > 1`. -/
theorem summable_farSourcePerronErrorTerm
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (farSourcePerronErrorTerm x c T) := by
  have hLSeries := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  have hBase : Summable (fun n : Nat =>
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c / T)
  exact Summable.of_nonneg_of_le
    (fun n => farSourcePerronErrorTerm_nonneg hx
      (le_trans zero_lt_one.le hc.le) hT n)
    (farSourcePerronErrorTerm_le_base hx hT)
    hBase

/-- The complete far range is at most `x ^ c / T` times the von Mangoldt
L-series norm sum. -/
theorem tsum_farSourcePerronErrorTerm_le
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    tsum (farSourcePerronErrorTerm x c T) <=
      ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c := by
  have hLSeries := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  have hBase : Summable (fun n : Nat =>
      ((x : Real) ^ c / T) *
        norm (LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c / T)
  calc
    tsum (farSourcePerronErrorTerm x c T) <=
        tsum (fun n : Nat =>
          ((x : Real) ^ c / T) *
            norm (LSeries.term
              (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
              (c : Complex) n)) :=
      (summable_farSourcePerronErrorTerm hx hc hT).tsum_le_tsum
        (farSourcePerronErrorTerm_le_base hx hT) hBase
    _ = ((x : Real) ^ c / T) * vonMangoldtLSeriesNormSum c := by
      rw [tsum_mul_left]
      rfl

end BombieriVinogradov.SiegelWalfisz
