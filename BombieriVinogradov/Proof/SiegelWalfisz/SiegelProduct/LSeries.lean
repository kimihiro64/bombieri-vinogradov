import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Summability

/-!
# Analytic identification of the Siegel product

This module identifies the coefficient L-series with the four analytic factors on `Re(s) > 1`.
-/

set_option autoImplicit false

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterArithmetic_LSeries_eq_LFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = χ.LFunction s := by
  rw [LSeries_congr (fun hn ↦ (χ.apply_eq_toArithmeticFunction_apply hn).symm) s]
  exact (DirichletCharacter.LFunction_eq_LSeries χ hs).symm

theorem characterPairArithmetic_LSeries_eq_LFunction {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (characterPairArithmetic χ ψ) s =
      (DirichletCharacter.mul χ ψ).LFunction s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeries_eq_LFunction (DirichletCharacter.mul χ ψ) hs

/-- The Dirichlet series with nonnegative coefficients is the source's four-factor product. -/
theorem siegelProduct_LSeries_eq {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (siegelProductCoefficients χ ψ) s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s *
        (DirichletCharacter.mul χ ψ).LFunction s := by
  have hzeta : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hχ := characterArithmetic_LSeriesSummable χ hs
  have hψ := characterArithmetic_LSeriesSummable ψ hs
  have hpair := characterPairArithmetic_LSeriesSummable χ ψ hs
  rw [siegelProductCoefficients,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ) hpair,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ,
    ArithmeticFunction.LSeries_mul' hzeta hχ,
    characterArithmetic_LSeries_eq_LFunction χ hs,
    characterArithmetic_LSeries_eq_LFunction ψ hs,
    characterPairArithmetic_LSeries_eq_LFunction χ ψ hs]
  simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    ← ArithmeticFunction.natCoe_apply]

end BombieriVinogradov.SiegelWalfisz
