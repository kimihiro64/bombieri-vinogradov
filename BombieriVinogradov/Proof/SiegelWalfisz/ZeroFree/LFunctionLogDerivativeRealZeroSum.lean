import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardConstantRealPart
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernelSummability
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Real logarithmic derivative after Hadamard-constant cancellation

This module takes real parts in the L-function zero sum, moves `Re` through the
summable divisor series, and cancels the reciprocal-zero terms using `Re B`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Bchi Binv : Complex}
    (hBchi : IsCompletedLFunctionHadamardConstant chi Bchi)
    (hBinv : IsCompletedLFunctionHadamardConstant chi⁻¹ Binv)
    {s : Complex} (hs : 1 < s.re) :
    -(logDeriv chi.LFunction s).re =
      Real.log N / 2 + (logDeriv chi.gammaFactor s).re -
        ∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
  have hAway : forall p : SymmetricCompletedZeroIndex chi,
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p hEqual
    have hUpper :=
      (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
        hchi hPrimitive p).2
    rw [← hEqual] at hUpper
    linarith
  have hCombined :=
    summable_symmetricCompletedLFunction_logDerivTerms_divisorZeroIndex₀
      hchi hPrimitive hAway
  have hMapped :
      (∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p)).re =
        ∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    change Complex.reCLM
        (∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p)) = _
    rw [Complex.reCLM.map_tsum hCombined]
    congr 1
  have hFirst :=
    summable_symmetricCompletedLFunction_zeroKernel_re
      hchi hPrimitive hs
  have hSecond :=
    summable_symmetricCompletedLFunction_divisorZeroIndex₀_inv_re
      hchi hPrimitive
  have hSplit :
      (∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) =
        (∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re) +
          ∑' p : SymmetricCompletedZeroIndex chi,
            (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    simpa using hFirst.tsum_add hSecond
  have hLFunction :=
    logDeriv_LFunction_eq_hadamardConstant_add_zero_sum
      hchi hPrimitive hBchi hs
  have hConstant :=
    symmetricCompletedLFunction_hadamardConstant_re_eq_neg_tsum
      hchi hPrimitive hBchi hBinv
  rw [hLFunction]
  simp only [Complex.add_re, Complex.sub_re]
  rw [hMapped, hSplit, hConstant]
  simp
  rw [← Complex.natCast_log]
  rw [Complex.ofReal_re]
  ring

end BombieriVinogradov.SiegelWalfisz
