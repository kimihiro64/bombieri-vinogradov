import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardNoMonomial
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeZeroSum
import PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor

/-!
# The completed-function Hadamard constant

This module proves that evaluating the derivative of a no-monomial Hadamard
polynomial at zero gives a unique complex constant, independent of the chosen
factorization.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_hadamard_polynomial_derivative_eval_eq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {P Q : Polynomial Complex} {z : Complex}
    (hPfac : forall w : Complex,
      symmetricCompletedLFunction chi w =
        Complex.exp (Polynomial.eval w P) *
          Complex.Hadamard.divisorCanonicalProduct 1
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex) w)
    (hQfac : forall w : Complex,
      symmetricCompletedLFunction chi w =
        Complex.exp (Polynomial.eval w Q) *
          Complex.Hadamard.divisorCanonicalProduct 1
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex) w)
    (hz : forall p : Complex.Hadamard.divisorZeroIndex₀
        (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    Polynomial.eval z P.derivative = Polynomial.eval z Q.derivative := by
  let S : Complex :=
    ∑' p : Complex.Hadamard.divisorZeroIndex₀
        (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
      (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hP :=
    logDeriv_symmetricCompletedLFunction_eq_polynomial_derivative_add_tsum
      hchi hPrimitive hPfac hz
  have hQ :=
    logDeriv_symmetricCompletedLFunction_eq_polynomial_derivative_add_tsum
      hchi hPrimitive hQfac hz
  have hsum : Polynomial.eval z P.derivative + S =
      Polynomial.eval z Q.derivative + S := by
    rw [← hP, ← hQ]
  exact add_right_cancel hsum

theorem symmetricCompletedLFunction_hadamard_polynomial_derivative_eval_zero_eq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {P Q : Polynomial Complex}
    (hPfac : forall w : Complex,
      symmetricCompletedLFunction chi w =
        Complex.exp (Polynomial.eval w P) *
          Complex.Hadamard.divisorCanonicalProduct 1
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex) w)
    (hQfac : forall w : Complex,
      symmetricCompletedLFunction chi w =
        Complex.exp (Polynomial.eval w Q) *
          Complex.Hadamard.divisorCanonicalProduct 1
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex) w) :
    Polynomial.eval 0 P.derivative = Polynomial.eval 0 Q.derivative := by
  apply symmetricCompletedLFunction_hadamard_polynomial_derivative_eval_eq
    hchi hPrimitive hPfac hQfac
  intro p
  exact (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm

theorem existsUnique_symmetricCompletedLFunction_hadamardConstant
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    ∃! B : Complex,
      exists P : Polynomial Complex,
        P.degree <= 1 ∧
          (forall z : Complex,
            symmetricCompletedLFunction chi z =
              Complex.exp (Polynomial.eval z P) *
                Complex.Hadamard.divisorCanonicalProduct 1
                  (symmetricCompletedLFunction chi) (Set.univ : Set Complex) z) ∧
          B = Polynomial.eval 0 P.derivative := by
  choose P hDegree hFactorization using
    symmetricCompletedLFunction_hadamard_factorization_no_monomial hchi hPrimitive
  refine ExistsUnique.intro (Polynomial.eval 0 P.derivative) ?_ ?_
  · exact Exists.intro P
      (And.intro hDegree (And.intro hFactorization rfl))
  · intro B hB
    choose Q _hQDegree hQFactorization hBEq using hB
    rw [hBEq]
    exact
      (symmetricCompletedLFunction_hadamard_polynomial_derivative_eval_zero_eq
        hchi hPrimitive hFactorization hQFactorization).symm

end BombieriVinogradov.SiegelWalfisz
