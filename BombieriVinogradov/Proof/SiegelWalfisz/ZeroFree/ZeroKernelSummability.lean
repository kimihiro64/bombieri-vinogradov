import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedDivisorLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroRealSummability
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernel
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Summability of real zero kernels

This module proves nonnegativity and summability of the real kernels
`Re (1 / (s - rho))` to the right of one, retaining divisor multiplicities.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_zeroKernel_re_nonneg
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hs : 1 < s.re) (p : SymmetricCompletedZeroIndex chi) :
    0 ≤ (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
  rw [one_div]
  exact zeroKernel_re_nonneg hs
    (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
      hchi hPrimitive p).2.le

theorem summable_symmetricCompletedLFunction_zeroKernel_re
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hs : 1 < s.re) :
    Summable
      (fun p : SymmetricCompletedZeroIndex chi =>
        (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re) := by
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
  have hCombinedRe :
      Summable
        (fun p : SymmetricCompletedZeroIndex chi =>
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) := by
    have hMapped := Complex.reCLM.summable hCombined
    exact hMapped.congr (fun p => by rfl)
  have hReciprocalRe :=
    summable_symmetricCompletedLFunction_divisorZeroIndex₀_inv_re
      hchi hPrimitive
  have hDifference := hCombinedRe.sub hReciprocalRe
  exact hDifference.congr (fun p => by
    simp)

end BombieriVinogradov.SiegelWalfisz
