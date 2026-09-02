import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductFormula
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroDivisorValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndexOfLFunctionZero

/-!
# Critical-strip zero values

This module identifies the finite multiplicity-aware completed divisor
truncation with ordinary primitive L-function zeros at exactly the same points.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_zero_of_mem_criticalStripZeroTruncation
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} {p : SymmetricCompletedZeroIndex chi}
    (hp : p ∈ criticalStripZeroTruncation chi T) :
    chi.LFunction (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
  have hpStrip := mem_criticalStripZeroTruncation_iff.mp hp
  have hpRePos : 0 < (Complex.Hadamard.divisorZeroIndex₀_val p).re :=
    hpStrip.1
  have hCompleted :=
    symmetricCompletedLFunction_divisorZeroIndex₀_apply_eq_zero
      hchi hPrimitive p
  have hProduct :=
    DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
      chi hpRePos
  rw [symmetricCompletedLFunction, hProduct] at hCompleted
  have hN : (N : Complex) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have hNormalizationNe :
      (N : Complex) ^ ((Complex.Hadamard.divisorZeroIndex₀_val p) / 2) ≠ 0 := by
    simp [hN]
  have hGammaNe :
      chi.gammaFactor (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hpRePos
  have hInnerZero := (mul_eq_zero.mp hCompleted).resolve_left hNormalizationNe
  exact (mul_eq_zero.mp hInnerZero).resolve_right hGammaNe

theorem exists_mem_criticalStripZeroTruncation_of_LFunction_eq_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hsPos : 0 < s.re) (hsLt : s.re < 1)
    {T : Real} (hsHeight : |s.im| < T) (hzero : chi.LFunction s = 0) :
    exists p, p ∈ criticalStripZeroTruncation chi T ∧
      Complex.Hadamard.divisorZeroIndex₀_val p = s := by
  obtain ⟨p, hp⟩ :=
    exists_completedZeroIndex_of_LFunction_eq_zero
      hchi hPrimitive hsPos hzero
  refine Exists.intro p (And.intro ?_ hp)
  rw [mem_criticalStripZeroTruncation_iff, hp]
  exact And.intro hsPos (And.intro hsLt hsHeight)

end BombieriVinogradov.SiegelWalfisz
