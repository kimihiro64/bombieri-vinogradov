import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.CrossLevel

/-!
# Absolute convergence for the Siegel product

This module owns the convergence inputs for the four arithmetic factors on the half-plane `Re(s) > 1`.
-/

set_option autoImplicit false

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterPairArithmetic_eq_crossLevel {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    characterPairArithmetic χ ψ =
      toArithmeticFunction (DirichletCharacter.mul χ ψ ·) := by
  rw [characterPairArithmetic]
  apply toArithmeticFunction_congr
  intro n _
  exact (crossLevelMul_apply_nat χ ψ n).symm

theorem characterArithmetic_LSeriesSummable {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s fun hn ↦
    (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)

theorem characterPairArithmetic_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (characterPairArithmetic χ ψ) s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeriesSummable (DirichletCharacter.mul χ ψ) hs

theorem siegelProductCoefficients_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (siegelProductCoefficients χ ψ) s := by
  rw [siegelProductCoefficients]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
        (characterArithmetic_LSeriesSummable χ hs))
      (characterArithmetic_LSeriesSummable ψ hs))
    (characterPairArithmetic_LSeriesSummable χ ψ hs)

end BombieriVinogradov.SiegelWalfisz
