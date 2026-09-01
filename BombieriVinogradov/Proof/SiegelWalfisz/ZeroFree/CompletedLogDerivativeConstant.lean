import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardConstant
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeZeroSum
import PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Constant form of the completed-function logarithmic derivative

This module uses the derivative constancy of a degree-one polynomial to replace
the evaluation-dependent polynomial term by the canonical Hadamard constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant chi B)
    {z : Complex}
    (hz : forall p : Complex.Hadamard.divisorZeroIndex₀
        (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv (symmetricCompletedLFunction chi) z =
      B +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  choose P hDegree hFactorization hBEq using hB
  calc
    logDeriv (symmetricCompletedLFunction chi) z =
        Polynomial.eval z P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀
              (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
      logDeriv_symmetricCompletedLFunction_eq_polynomial_derivative_add_tsum
        hchi hPrimitive hFactorization hz
    _ = B +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
      rw [Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one
        hDegree z, ← hBEq]

theorem exists_symmetricCompletedLFunction_hadamardConstant_logDeriv_zero_sum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    exists B : Complex,
      IsCompletedLFunctionHadamardConstant chi B ∧
        forall z : Complex,
          (forall p : Complex.Hadamard.divisorZeroIndex₀
              (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
            z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) ->
          logDeriv (symmetricCompletedLFunction chi) z =
            B +
              ∑' p : Complex.Hadamard.divisorZeroIndex₀
                  (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
                (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
                  1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  choose P hDegree hFactorization using
    symmetricCompletedLFunction_hadamard_factorization_no_monomial hchi hPrimitive
  let B : Complex := Polynomial.eval 0 P.derivative
  have hB : IsCompletedLFunctionHadamardConstant chi B :=
    Exists.intro P (And.intro hDegree (And.intro hFactorization rfl))
  refine Exists.intro B (And.intro hB ?_)
  intro z hz
  exact logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
    hchi hPrimitive hB hz

end BombieriVinogradov.SiegelWalfisz
