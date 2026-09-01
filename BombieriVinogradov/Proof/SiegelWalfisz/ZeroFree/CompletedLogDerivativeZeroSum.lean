import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedDivisorLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardNoMonomial
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence

/-!
# Logarithmic derivative as a sum over completed-function zeros

This module differentiates a chosen no-monomial Hadamard factorization of the
primitive symmetric completed Dirichlet L-function. The sum remains indexed by the
divisor, so zero multiplicities are retained.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_symmetricCompletedLFunction_eq_polynomial_derivative_add_tsum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {P : Polynomial Complex} {z : Complex}
    (hfac : forall w : Complex,
      symmetricCompletedLFunction chi w =
        Complex.exp (Polynomial.eval w P) *
          Complex.Hadamard.divisorCanonicalProduct 1
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex) w)
    (hz : forall p : Complex.Hadamard.divisorZeroIndex₀
        (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv (symmetricCompletedLFunction chi) z =
      Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let G : Complex -> Complex :=
    Complex.Hadamard.divisorCanonicalProduct 1
      (symmetricCompletedLFunction chi) (Set.univ : Set Complex)
  have hfun : symmetricCompletedLFunction chi =
      fun w : Complex => Complex.exp (Polynomial.eval w P) * G w := by
    funext w
    simpa [G] using hfac w
  have hdiffExp : DifferentiableAt Complex
      (fun w : Complex => Complex.exp (Polynomial.eval w P)) z :=
    ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z
      (P.hasDerivAt z)).differentiableAt
  have hprodNe :
      Complex.Hadamard.divisorCanonicalProduct 1
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex) z ≠ 0 :=
    Complex.Hadamard.divisorCanonicalProduct_ne_zero_of_forall_ne
      1 (symmetricCompletedLFunction chi)
      (summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq
        hchi hPrimitive) hz
  calc
    logDeriv (symmetricCompletedLFunction chi) z =
        logDeriv
          (fun w : Complex => Complex.exp (Polynomial.eval w P) * G w) z := by
      rw [hfun]
    _ = logDeriv (fun w : Complex => Complex.exp (Polynomial.eval w P)) z +
        logDeriv G z := by
      exact logDeriv_mul z (Complex.exp_ne_zero _)
        (by simpa [G] using hprodNe) hdiffExp
        (by
          simpa [G] using
            Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ
              1 (symmetricCompletedLFunction chi)
              (summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq
                hchi hPrimitive) z)
    _ = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀
            (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
      rw [Polynomial.logDeriv_exp_eval]
      rw [show logDeriv G z =
          ∑' p : Complex.Hadamard.divisorZeroIndex₀
              (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) from
        by
          simpa [G] using
            logDeriv_symmetricCompletedLFunction_divisorCanonicalProduct_one_eq_tsum
              hchi hPrimitive hz]

theorem exists_symmetricCompletedLFunction_logDeriv_zero_sum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    exists P : Polynomial Complex,
      P.degree <= 1 ∧
        forall z : Complex,
          (forall p : Complex.Hadamard.divisorZeroIndex₀
              (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
            z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) ->
          logDeriv (symmetricCompletedLFunction chi) z =
            Polynomial.eval z P.derivative +
              ∑' p : Complex.Hadamard.divisorZeroIndex₀
                  (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
                (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
                  1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  choose P hDegree hFactorization using
    symmetricCompletedLFunction_hadamard_factorization_no_monomial hchi hPrimitive
  refine Exists.intro P (And.intro hDegree ?_)
  intro z hz
  exact logDeriv_symmetricCompletedLFunction_eq_polynomial_derivative_add_tsum
    hchi hPrimitive hFactorization hz

end BombieriVinogradov.SiegelWalfisz
