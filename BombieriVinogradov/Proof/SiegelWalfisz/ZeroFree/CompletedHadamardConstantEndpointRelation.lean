import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedDivisorEndpoints
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeConstant
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeReflection
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor

/-!
# Endpoint relation for completed-function Hadamard constants

This module evaluates the zero-sum at zero and combines its value at one with the
logarithmic-derivative functional equation. The result relates the canonical constants
for a primitive character and its inverse.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_symmetricCompletedLFunction_zero_eq_hadamardConstant
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {B : Complex} (hB : IsCompletedLFunctionHadamardConstant chi B) :
    logDeriv (symmetricCompletedLFunction chi) 0 = B := by
  have hFormula :=
    logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
      hchi hPrimitive hB
      (z := (0 : Complex))
      (fun p => (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm)
  have hTermsZero :
      (fun p : Complex.Hadamard.divisorZeroIndex₀
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex) =>
        1 / ((0 : Complex) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
    funext p
    simp
  have hZeroSum :
      (∑' p : Complex.Hadamard.divisorZeroIndex₀
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
        (1 / ((0 : Complex) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p)) = 0 := by
    rw [hTermsZero]
    exact tsum_zero
  rw [hZeroSum, add_zero] at hFormula
  exact hFormula

theorem symmetricCompletedLFunction_hadamardConstant_add_inv_eq_neg_tsum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Bchi Binv : Complex}
    (hBchi : IsCompletedLFunctionHadamardConstant chi Bchi)
    (hBinv : IsCompletedLFunctionHadamardConstant chi⁻¹ Binv) :
    Bchi + Binv =
      -∑' p : Complex.Hadamard.divisorZeroIndex₀
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
        (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  have hInverseNe : chi⁻¹ ≠ 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hPrimitiveInv : DirichletCharacter.IsPrimitive chi⁻¹ :=
    BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  let S : Complex :=
    ∑' p : Complex.Hadamard.divisorZeroIndex₀
        (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
      (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hAtOne : logDeriv (symmetricCompletedLFunction chi) 1 = Bchi + S := by
    simpa [S] using
      (logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
        hchi hPrimitive hBchi
        (z := (1 : Complex))
        (symmetricCompletedLFunction_one_ne_divisorZeroIndex₀_val
          hchi hPrimitive))
  have hAtZeroInv :
      logDeriv (symmetricCompletedLFunction chi⁻¹) 0 = Binv :=
    logDeriv_symmetricCompletedLFunction_zero_eq_hadamardConstant
      hInverseNe hPrimitiveInv hBinv
  have hReflection :
      logDeriv (symmetricCompletedLFunction chi) 1 =
        -logDeriv (symmetricCompletedLFunction chi⁻¹) 0 := by
    simpa using
      (logDeriv_symmetricCompletedLFunction_one_sub
        hchi hPrimitive (0 : Complex))
  have hMain : Bchi + S = -Binv := by
    calc
      Bchi + S = logDeriv (symmetricCompletedLFunction chi) 1 := hAtOne.symm
      _ = -logDeriv (symmetricCompletedLFunction chi⁻¹) 0 := hReflection
      _ = -Binv := by rw [hAtZeroInv]
  change Bchi + Binv = -S
  linear_combination hMain

end BombieriVinogradov.SiegelWalfisz
