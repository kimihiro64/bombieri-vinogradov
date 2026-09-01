import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeConstant
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip

/-!
# Dirichlet L-function logarithmic derivative as a zero sum

This module proves the zero-sum form of Strombergsson Proposition 10.7. The gamma
factor remains packaged as its logarithmic derivative for a later, separate digamma
expansion and bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_LFunction_eq_hadamardConstant_add_zero_sum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {B : Complex} (hB : IsCompletedLFunctionHadamardConstant chi B)
    {s : Complex} (hs : 1 < s.re) :
    logDeriv chi.LFunction s =
      -(Real.log N : Complex) / 2 - logDeriv chi.gammaFactor s + B +
        ∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  have hAway : forall p : SymmetricCompletedZeroIndex chi,
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p hEqual
    have hUpper :=
      (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
        hchi hPrimitive p).2
    rw [← hEqual] at hUpper
    linarith
  have hHadamard :=
    logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
      hchi hPrimitive hB hAway
  have hProduct :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors hchi hs
  calc
    logDeriv chi.LFunction s =
        logDeriv (symmetricCompletedLFunction chi) s -
          (Real.log N : Complex) / 2 - logDeriv chi.gammaFactor s := by
      rw [hProduct]
      ring
    _ = -(Real.log N : Complex) / 2 - logDeriv chi.gammaFactor s + B +
        ∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
      rw [hHadamard]
      ring

end BombieriVinogradov.SiegelWalfisz
