import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticPositiveZeroGap
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticConjugateZeroIndex

/-!
# Uniform gap for every nonreal primitive quadratic zero

Positive imaginary parts are covered directly. Negative imaginary parts are
transferred to the multiplicity-aware conjugate divisor index.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_nonrealZero_gap :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
            forall p : SymmetricCompletedZeroIndex chi,
              (Complex.Hadamard.divisorZeroIndex₀_val p).im ≠ 0 ->
                c / (Real.log N + Real.log
                  (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2)) ≤
                  1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  obtain ⟨c, hcPos, hPositive⟩ :=
    exists_primitive_quadratic_positiveZero_gap
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive hchiSquare p hpNonreal
  by_cases hpPos : 0 < (Complex.Hadamard.divisorZeroIndex₀_val p).im
  · exact hPositive hNLower hchi hPrimitive hchiSquare p hpPos
  · have hpNeg : (Complex.Hadamard.divisorZeroIndex₀_val p).im < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpPos) hpNonreal
    obtain ⟨q, hq⟩ :=
      exists_quadratic_conjugateZeroIndex hchi hPrimitive hchiSquare p
    have hqRe := congrArg Complex.re hq
    have hqIm := congrArg Complex.im hq
    simp only [Complex.conj_re] at hqRe
    simp only [Complex.conj_im] at hqIm
    have hqPos : 0 < (Complex.Hadamard.divisorZeroIndex₀_val q).im := by
      rw [hqIm]
      linarith
    have hGap := hPositive hNLower hchi hPrimitive hchiSquare q hqPos
    rw [hqRe, hqIm, abs_neg] at hGap
    exact hGap

end BombieriVinogradov.SiegelWalfisz
