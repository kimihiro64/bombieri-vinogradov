import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFiniteOrder
import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order

/-!
# Hadamard factorization of a completed Dirichlet L-function

This module proves nontriviality at one right-half-plane point and applies the general
finite-order theorem to obtain the genus-one divisor canonical product.
-/

set_option autoImplicit false

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_two_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) :
    symmetricCompletedLFunction chi 2 ≠ 0 := by
  have hNNeOne : N ≠ 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hGammaNe : chi.gammaFactor 2 ≠ 0 := by
    rcases chi.even_or_odd with hEven | hOdd
    · rw [hEven.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
    · rw [hOdd.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hCompleted : chi.completedLFunction 2 =
      chi.LFunction 2 * chi.gammaFactor 2 := by
    exact ((eq_div_iff hGammaNe).mp
      (chi.LFunction_eq_completed_div_gammaFactor 2 (.inr hNNeOne))).symm
  have hLFunction : chi.LFunction 2 ≠ 0 :=
    chi.LFunction_ne_zero_of_one_le_re (.inl hchi) (by norm_num)
  rw [symmetricCompletedLFunction, hCompleted]
  apply mul_ne_zero
  · have hNCast : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
    simpa using hNCast
  · exact mul_ne_zero hLFunction hGammaNe

theorem symmetricCompletedLFunction_hadamard_factorization
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    exists P : Polynomial Complex,
      P.degree ≤ 1 ∧ forall z : Complex,
        symmetricCompletedLFunction chi z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt (symmetricCompletedLFunction chi) 0) *
            Complex.Hadamard.divisorCanonicalProduct 1
              (symmetricCompletedLFunction chi) (Set.univ : Set Complex) z := by
  obtain ⟨P, hDegree, hFactorization⟩ :=
    Complex.Hadamard.hadamard_factorization_of_order
      (f := symmetricCompletedLFunction chi) (ρ := (1 : Real))
      (by norm_num) ⟨2, symmetricCompletedLFunction_two_ne_zero hchi⟩
      (symmetricCompletedLFunction_entireOfOrderAtMost_one hchi hPrimitive)
  have hFloor : Nat.floor (1 : Real) = 1 := by norm_num
  rw [hFloor] at hDegree hFactorization
  exact ⟨P, hDegree, hFactorization⟩

end BombieriVinogradov.SiegelWalfisz
