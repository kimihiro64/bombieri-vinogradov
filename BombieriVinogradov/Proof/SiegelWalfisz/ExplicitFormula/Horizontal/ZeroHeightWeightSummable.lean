import BombieriVinogradov.Helpers.ComplexAnalysis.ReciprocalVerticalKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernelSummability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Summability of quadratic vertical zero weights

This module converts the summable reciprocal zero kernel at real part two
into summability of the quadratic weight in the vertical distance from a
given height.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The quadratic vertical-gap weight is summable over completed zeros,
including their divisor multiplicities. -/
theorem summable_zero_vertical_weight
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) :
    Summable (fun p : SymmetricCompletedZeroIndex chi =>
      1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)) := by
  let s : Complex := ((2 : Real) : Complex) +
    (T : Complex) * Complex.I
  have hsRight : 1 < s.re := by
    dsimp [s]
    simp [Complex.mul_re]
  have hKernelSummable :
      Summable (fun p : SymmetricCompletedZeroIndex chi =>
        (1 / (s - symmetricCompletedZeroValue p)).re) := by
    simpa [symmetricCompletedZeroValue] using
      summable_symmetricCompletedLFunction_zeroKernel_re
        hchi hPrimitive hsRight
  have hWeightNonneg : forall p : SymmetricCompletedZeroIndex chi,
      0 <= 1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2) := by
    intro p
    exact div_nonneg (by norm_num)
      (by nlinarith [sq_nonneg (T - (symmetricCompletedZeroValue p).im)])
  have hWeightPointwise : forall p : SymmetricCompletedZeroIndex chi,
      1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2) <=
        4 * (1 / (s - symmetricCompletedZeroValue p)).re := by
    intro p
    have hStrip : Set.Ioo 0 1 (symmetricCompletedZeroValue p).re :=
      symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p
    have hKernel :=
      BombieriVinogradov.ComplexAnalysis.one_div_vertical_gap_sq_le_zeroKernel_re
        (T := T) hStrip.1 hStrip.2
    rw [show s = ((2 : Real) : Complex) +
        (T : Complex) * Complex.I by rfl]
    calc
      1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2) =
        4 * (1 / (4 *
          (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2))) := by
          field_simp
      _ <= 4 * (1 /
          (((2 : Real) : Complex) + (T : Complex) * Complex.I -
            symmetricCompletedZeroValue p)).re :=
        mul_le_mul_of_nonneg_left hKernel (by norm_num)
  exact Summable.of_nonneg_of_le hWeightNonneg hWeightPointwise
    (hKernelSummable.mul_left 4)

end BombieriVinogradov.SiegelWalfisz
