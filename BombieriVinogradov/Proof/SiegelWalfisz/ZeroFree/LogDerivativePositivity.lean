import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.EulerTermIdentity

/-!
# Positivity of the three logarithmic derivatives

This module sums the nonnegative Euler weights and proves Strombergsson
Lemma 11.2 for analytically continued Dirichlet L-functions on `re s > 1`.
-/

set_option autoImplicit false

open ArithmeticFunction hiding log
open Complex
open scoped LSeries.notation

namespace BombieriVinogradov.SiegelWalfisz

/-- Strombergsson Lemma 11.2, equation (397). -/
theorem logDerivative_combination_nonneg {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) {sigma : ℝ} (hsigma : 1 < sigma)
    (t : ℝ) :
    0 ≤
      3 * (-deriv (1 : DirichletCharacter ℂ N).LFunction sigma /
          (1 : DirichletCharacter ℂ N).LFunction sigma).re +
      4 * (-deriv chi.LFunction ((sigma : ℂ) + Complex.I * t) /
          chi.LFunction ((sigma : ℂ) + Complex.I * t)).re +
      (-deriv (chi ^ 2).LFunction ((sigma : ℂ) + 2 * Complex.I * t) /
          (chi ^ 2).LFunction ((sigma : ℂ) + 2 * Complex.I * t)).re := by
  have hsigmaComplex : 1 < (sigma : ℂ).re := by simpa
  have hsigmaOne : 1 < ((sigma : ℂ) + Complex.I * t).re := by
    simpa [Complex.mul_re] using hsigma
  have hsigmaTwo : 1 < ((sigma : ℂ) + 2 * Complex.I * t).re := by
    simpa [Complex.mul_re] using hsigma
  rw [neg_logDeriv_LFunction_eq_twist_vonMangoldt
      (1 : DirichletCharacter ℂ N) hsigmaComplex,
    neg_logDeriv_LFunction_eq_twist_vonMangoldt chi hsigmaOne,
    neg_logDeriv_LFunction_eq_twist_vonMangoldt (chi ^ 2) hsigmaTwo]
  have hsumZero :=
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      (1 : DirichletCharacter ℂ N) hsigmaComplex).LSeriesHasSum
  have hsumOne :=
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hsigmaOne).LSeriesHasSum
  have hsumTwo :=
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi ^ 2)
      hsigmaTwo).LSeriesHasSum
  have hcombined :
      HasSum
        (fun n : ℕ ↦
          3 * (LSeries.term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) sigma n).re +
          4 * (LSeries.term (↗chi * ↗Λ)
            ((sigma : ℂ) + Complex.I * t) n).re +
          (LSeries.term (↗(chi ^ 2) * ↗Λ)
            ((sigma : ℂ) + 2 * Complex.I * t) n).re)
        (3 * (L (↗(1 : DirichletCharacter ℂ N) * ↗Λ) sigma).re +
          4 * (L (↗chi * ↗Λ) ((sigma : ℂ) + Complex.I * t)).re +
          (L (↗(chi ^ 2) * ↗Λ)
            ((sigma : ℂ) + 2 * Complex.I * t)).re) := by
    exact (((hasSum_re hsumZero).mul_left 3).add
      ((hasSum_re hsumOne).mul_left 4)).add (hasSum_re hsumTwo)
  calc
    0 ≤ ∑' n : ℕ,
        (3 * (LSeries.term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) sigma n).re +
          4 * (LSeries.term (↗chi * ↗Λ)
            ((sigma : ℂ) + Complex.I * t) n).re +
          (LSeries.term (↗(chi ^ 2) * ↗Λ)
            ((sigma : ℂ) + 2 * Complex.I * t) n).re) := by
      apply tsum_nonneg
      intro n
      rw [logDerivativeEulerTerms_eq_weight]
      exact zeroFreeEulerWeight_nonneg chi sigma t n
    _ = 3 * (L (↗(1 : DirichletCharacter ℂ N) * ↗Λ) sigma).re +
          4 * (L (↗chi * ↗Λ) ((sigma : ℂ) + Complex.I * t)).re +
          (L (↗(chi ^ 2) * ↗Λ)
            ((sigma : ℂ) + 2 * Complex.I * t)).re := hcombined.tsum_eq

end BombieriVinogradov.SiegelWalfisz
