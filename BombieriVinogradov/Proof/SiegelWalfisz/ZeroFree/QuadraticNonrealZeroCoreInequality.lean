import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ConjugatePairKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticConjugateZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.TwoZeroLogDerivativeBound
import Mathlib.Tactic.Linarith

/-!
# Core inequality for a nonreal quadratic zero

This is Strombergsson equation (410), expressed for one multiplicity-indexed
zero in the upper half-plane and its distinct conjugate index.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_quadratic_nonrealZero_core_inequality :
    exists K : Real, 0 < K ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
            forall p : SymmetricCompletedZeroIndex chi,
              0 < (Complex.Hadamard.divisorZeroIndex₀_val p).im ->
                forall {sigma : Real}, 1 < sigma -> sigma ≤ 2 ->
                  2 * (sigma -
                    (Complex.Hadamard.divisorZeroIndex₀_val p).re) /
                    ((sigma -
                      (Complex.Hadamard.divisorZeroIndex₀_val p).re) ^ 2 +
                      (Complex.Hadamard.divisorZeroIndex₀_val p).im ^ 2) ≤
                    (sigma - 1)⁻¹ + K * Real.log N := by
  obtain ⟨K, hKPos, hTwoZero⟩ := exists_twoZero_logDerivative_bound
  refine Exists.intro K (And.intro hKPos ?_)
  intro N _hN hNLower chi hchi hPrimitive hchiSquare p hpIm
    sigma hsigma hsigmaUpper
  obtain ⟨q, hq⟩ :=
    exists_quadratic_conjugateZeroIndex hchi hPrimitive hchiSquare p
  have hpq : p ≠ q := by
    intro hEqual
    subst q
    have hImaginary := congrArg Complex.im hq
    simp only [Complex.conj_im] at hImaginary
    linarith
  have hBound :=
    hTwoZero hNLower hchi hPrimitive p q hpq hsigma hsigmaUpper
  rw [hq, conjugatePairKernel_re] at hBound
  exact hBound

end BombieriVinogradov.SiegelWalfisz
