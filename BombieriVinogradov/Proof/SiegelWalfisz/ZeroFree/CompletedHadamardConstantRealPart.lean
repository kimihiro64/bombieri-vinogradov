import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardConstantConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardConstantEndpointRelation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroRealSumReflection
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Real part of the completed-function Hadamard constant

This module proves the published identity identifying the real part of the canonical
Hadamard constant with the negative sum of the real reciprocal zero terms.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_hadamardConstant_re_eq_neg_tsum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Bchi Binv : Complex}
    (hBchi : IsCompletedLFunctionHadamardConstant chi Bchi)
    (hBinv : IsCompletedLFunctionHadamardConstant chi⁻¹ Binv) :
    Bchi.re =
      -∑' p : SymmetricCompletedZeroIndex chi,
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  have hCombined :
      Summable
        (fun p : SymmetricCompletedZeroIndex chi =>
          1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
    summable_symmetricCompletedLFunction_logDerivTerms_divisorZeroIndex₀
      hchi hPrimitive
      (symmetricCompletedLFunction_one_ne_divisorZeroIndex₀_val
        hchi hPrimitive)
  have hFirst :
      Summable
        (fun p : SymmetricCompletedZeroIndex chi =>
          (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p)).re) :=
    summable_symmetricCompletedLFunction_divisorZeroIndex₀_one_sub_inv_re
      hchi hPrimitive
  have hSecond :
      Summable
        (fun p : SymmetricCompletedZeroIndex chi =>
          (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) :=
    summable_symmetricCompletedLFunction_divisorZeroIndex₀_inv_re
      hchi hPrimitive
  have hEndpoint :=
    symmetricCompletedLFunction_hadamardConstant_add_inv_eq_neg_tsum
      hchi hPrimitive hBchi hBinv
  have hEndpointRe :
      (Bchi + Binv).re =
        -∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    change Complex.reCLM (Bchi + Binv) = _
    rw [hEndpoint, map_neg, Complex.reCLM.map_tsum hCombined]
    congr 1
  have hSplit :
      (∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) =
        (∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p)).re) +
          ∑' p : SymmetricCompletedZeroIndex chi,
            (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    simpa using hFirst.tsum_add hSecond
  have hConjugate :=
    symmetricCompletedLFunction_hadamardConstant_inv_eq_conj
      hchi hPrimitive hBchi hBinv
  have hLeft : (Bchi + Binv).re = 2 * Bchi.re := by
    rw [hConjugate]
    simp
    ring
  have hReindexed :=
    tsum_symmetricCompletedLFunction_divisorZeroIndex₀_one_sub_inv_re_eq
      hchi hPrimitive
  rw [hLeft, hSplit, hReindexed] at hEndpointRe
  linarith

end BombieriVinogradov.SiegelWalfisz
