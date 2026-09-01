import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernelSummability

/-!
# Monotonicity of selected zero-kernel sums

This module shows that any subset of the nonnegative multiplicity-indexed zero kernels
has total mass at most the full zero-kernel sum.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem tsum_symmetricCompletedLFunction_zeroKernel_subtype_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hs : 1 < s.re)
    (selected : Set (SymmetricCompletedZeroIndex chi)) :
    (∑' p : selected,
        (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p.1)).re) ≤
      ∑' p : SymmetricCompletedZeroIndex chi,
        (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
  exact
    (summable_symmetricCompletedLFunction_zeroKernel_re hchi hPrimitive hs).tsum_subtype_le
      (fun p : SymmetricCompletedZeroIndex chi =>
        (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re)
      selected
      (symmetricCompletedLFunction_zeroKernel_re_nonneg hchi hPrimitive hs)

end BombieriVinogradov.SiegelWalfisz
