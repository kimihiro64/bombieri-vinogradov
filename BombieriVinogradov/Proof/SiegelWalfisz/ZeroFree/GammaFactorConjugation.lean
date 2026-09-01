import BombieriVinogradov.Helpers.DirichletCharacter.ComplexConjugation
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Conjugation of Dirichlet gamma factors

This module proves complex-conjugation identities for Deligne's real gamma factor and
the parity-selected Dirichlet gamma factor.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace BombieriVinogradov.SiegelWalfisz

theorem Complex.Gammaℝ_conj (s : Complex) :
    Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  have hArg : Complex.arg (Real.pi : Complex) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hPow := Complex.cpow_conj (Real.pi : Complex) (-s / 2) hArg
  have hGamma := Complex.Gamma_conj (s / 2)
  simp only [map_neg, map_div₀, map_ofNat] at hPow hGamma
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · simpa using hPow

theorem DirichletCharacter.gammaFactor_inv_eq_conj_conj
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex) :
    chi⁻¹.gammaFactor s = conj (chi.gammaFactor (conj s)) := by
  rcases chi.even_or_odd with hEven | hOdd
  · have hEvenInv : DirichletCharacter.Even chi⁻¹ :=
      BombieriVinogradov.DirichletCharacter.Even.inv hEven
    rw [hEvenInv.gammaFactor_def, hEven.gammaFactor_def]
    simpa using Complex.Gammaℝ_conj (conj s)
  · have hOddInv : DirichletCharacter.Odd chi⁻¹ :=
      BombieriVinogradov.DirichletCharacter.Odd.inv hOdd
    rw [hOddInv.gammaFactor_def, hOdd.gammaFactor_def]
    simpa using Complex.Gammaℝ_conj (conj s + 1)

end BombieriVinogradov.SiegelWalfisz
