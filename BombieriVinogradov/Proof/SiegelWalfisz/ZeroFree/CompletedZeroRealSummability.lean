import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroSummability
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summability of real reciprocal zero terms

This module bounds `Re (1 / rho)` by the compiled inverse-square zero majorant,
using that every divisor-indexed zero lies in the critical strip.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_divisorZeroIndex₀_inv_re_nonneg
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    0 <= (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  let rho := Complex.Hadamard.divisorZeroIndex₀_val p
  have hRe : 0 < rho.re :=
    (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
      hchi hPrimitive p).1
  have hNormSq : 0 < Complex.normSq rho :=
    Complex.normSq_pos.mpr p.property
  rw [one_div, Complex.inv_re]
  exact div_nonneg hRe.le hNormSq.le

theorem symmetricCompletedLFunction_divisorZeroIndex₀_inv_re_le_norm_inv_sq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re <=
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : Nat) := by
  let rho := Complex.Hadamard.divisorZeroIndex₀_val p
  have hRe : rho.re < 1 :=
    (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
      hchi hPrimitive p).2
  have hNormSq : 0 < Complex.normSq rho :=
    Complex.normSq_pos.mpr p.property
  rw [one_div, Complex.inv_re]
  calc
    rho.re / Complex.normSq rho <= 1 / Complex.normSq rho :=
      (div_le_div_iff_of_pos_right hNormSq).2 hRe.le
    _ = ‖rho‖⁻¹ ^ (2 : Nat) := by
      rw [Complex.normSq_eq_norm_sq]
      simp [one_div]

theorem summable_symmetricCompletedLFunction_divisorZeroIndex₀_inv_re
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Summable
      (fun p : SymmetricCompletedZeroIndex chi =>
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) :=
  Summable.of_nonneg_of_le
    (symmetricCompletedLFunction_divisorZeroIndex₀_inv_re_nonneg
      hchi hPrimitive)
    (symmetricCompletedLFunction_divisorZeroIndex₀_inv_re_le_norm_inv_sq
      hchi hPrimitive)
    (summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq
      hchi hPrimitive)

end BombieriVinogradov.SiegelWalfisz
