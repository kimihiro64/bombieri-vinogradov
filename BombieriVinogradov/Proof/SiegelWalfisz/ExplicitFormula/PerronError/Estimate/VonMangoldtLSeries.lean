import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Von Mangoldt L-series norm identity

This module identifies the positive norm series used by the Perron-error
majorant with the real part of the logarithmic derivative of zeta.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The norm sum of the von Mangoldt Dirichlet series on the real axis. -/
def vonMangoldtLSeriesNormSum (c : Real) : Real :=
  tsum (fun n : Nat =>
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n))

/-- Each von Mangoldt L-series term at a real argument is real. -/
theorem LSeriesTerm_vonMangoldt_eq_ofReal
    {c : Real} (n : Nat) :
    LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n =
      ((ArithmeticFunction.vonMangoldt n / (n : Real) ^ c : Real) : Complex) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [LSeries.term_def]
  case neg =>
    rw [LSeries.term_def, if_neg hn]
    rw [Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n) c]
    norm_cast

/-- Positivity makes the real part of each term equal to its norm. -/
theorem re_LSeriesTerm_vonMangoldt_eq_norm
    {c : Real} (n : Nat) :
    (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n).re =
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) := by
  rw [LSeriesTerm_vonMangoldt_eq_ofReal]
  rw [Complex.ofReal_re, Complex.norm_real]
  apply Eq.symm
  rw [Real.norm_of_nonneg]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) c)

/-- The norm of a real-axis von Mangoldt L-series term is its nonnegative
real Dirichlet coefficient. -/
theorem norm_LSeriesTerm_vonMangoldt_eq
    {c : Real} (n : Nat) :
    norm (LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (c : Complex) n) =
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ c := by
  rw [LSeriesTerm_vonMangoldt_eq_ofReal, Complex.norm_real,
    Real.norm_of_nonneg]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) c)

/-- On `c > 1`, the norm sum is the real logarithmic derivative of zeta. -/
theorem vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re
    {c : Real} (hc : 1 < c) :
    vonMangoldtLSeriesNormSum c =
      (-deriv riemannZeta (c : Complex) / riemannZeta (c : Complex)).re := by
  have hSummable := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : Complex)) (by simpa using hc)
  have hSeries := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (c : Complex)) (by simpa using hc)
  rw [LSeries] at hSeries
  have hReal := congrArg Complex.re hSeries
  rw [Complex.re_tsum hSummable] at hReal
  have hTerms : (fun n : Nat =>
      (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n).re) = fun n : Nat =>
      norm (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n) := by
    funext n
    exact re_LSeriesTerm_vonMangoldt_eq_norm n
  rw [hTerms] at hReal
  exact hReal

end BombieriVinogradov.SiegelWalfisz
