import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroDivisorReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroRealSummability

/-!
# Reindexing the real reciprocal zero sum

This module reindexes the real reciprocal terms through the multiplicity-preserving
zero-divisor involution.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedZeroReflection_one_sub_inv_re
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val
        (symmetricCompletedZeroReflectionEquiv hchi hPrimitive p))).re =
      (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  rw [symmetricCompletedZeroReflectionEquiv_val]
  have hDenominator :
      (1 : Complex) -
          (1 - (starRingEnd Complex)
            (Complex.Hadamard.divisorZeroIndex₀_val p)) =
        (starRingEnd Complex)
          (Complex.Hadamard.divisorZeroIndex₀_val p) := by
    ring
  rw [hDenominator, one_div]
  rw [← map_inv₀ (starRingEnd Complex)]
  simp

theorem summable_symmetricCompletedLFunction_divisorZeroIndex₀_one_sub_inv_re
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Summable
      (fun p : SymmetricCompletedZeroIndex chi =>
        (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p)).re) := by
  let e := symmetricCompletedZeroReflectionEquiv hchi hPrimitive
  let f : SymmetricCompletedZeroIndex chi -> Real :=
    fun p => (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p)).re
  let g : SymmetricCompletedZeroIndex chi -> Real :=
    fun p => (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re
  have hPointwise : f ∘ e = g := by
    funext p
    exact symmetricCompletedZeroReflection_one_sub_inv_re hchi hPrimitive p
  have hG : Summable g :=
    summable_symmetricCompletedLFunction_divisorZeroIndex₀_inv_re
      hchi hPrimitive
  have hCompose : Summable (f ∘ e) := by
    rw [hPointwise]
    exact hG
  exact e.summable_iff.mp hCompose

theorem tsum_symmetricCompletedLFunction_divisorZeroIndex₀_one_sub_inv_re_eq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    (∑' p : SymmetricCompletedZeroIndex chi,
        (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p)).re) =
      ∑' p : SymmetricCompletedZeroIndex chi,
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  let e := symmetricCompletedZeroReflectionEquiv hchi hPrimitive
  let f : SymmetricCompletedZeroIndex chi -> Real :=
    fun p => (1 / (1 - Complex.Hadamard.divisorZeroIndex₀_val p)).re
  let g : SymmetricCompletedZeroIndex chi -> Real :=
    fun p => (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re
  have hPointwise : f ∘ e = g := by
    funext p
    exact symmetricCompletedZeroReflection_one_sub_inv_re hchi hPrimitive p
  have hReindexed := e.tsum_eq f
  have hReindexedFunction : (fun p => f (e p)) = g := by
    simpa [Function.comp_def] using hPointwise
  rw [hReindexedFunction] at hReindexed
  simpa [f, g] using hReindexed.symm

end BombieriVinogradov.SiegelWalfisz
