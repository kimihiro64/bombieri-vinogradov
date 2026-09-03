import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.HorizontalKernelBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.DifferenceOrdinateBounds
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Pointwise centered term bound for newly retained zeros

This module bounds one centered zero term using its critical-strip real part
and the old cutoff's lower bound on its absolute ordinate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_centeredZeroTerm_of_mem_cutoffDifference_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {x : Nat} (hx : 2 < x) {T Tprime : Real} (hT : 2 <= T)
    {exceptional : Option Complex}
    {p : SymmetricCompletedZeroIndex chi}
    (hp :
      (retainedCriticalZeroCutoffDifference chi T Tprime exceptional :
        Set (SymmetricCompletedZeroIndex chi)) p) :
    norm
        (((x : Complex) ^ symmetricCompletedZeroValue p - 1) /
          symmetricCompletedZeroValue p) <=
      4 * (x : Real) / T := by
  have hpDifference :=
    mem_retainedCriticalZeroCutoffDifference_iff.mp hp
  have hpRetained :=
    mem_retainedCriticalZeroIndices_iff.mp hpDifference.1
  have hpStrip :=
    mem_criticalStripZeroTruncation_iff.mp hpRetained.1
  have hpReLt :
      (symmetricCompletedZeroValue p).re < 1 := by
    simpa [symmetricCompletedZeroValue] using hpStrip.2.1
  have hpReLine :
      (symmetricCompletedZeroValue p).re <=
        optimizedPerronLine x :=
    (hpReLt.trans (optimizedPerronLine_gt_one hx)).le
  have hBounds :=
    abs_im_bounds_of_mem_retainedCriticalZeroCutoffDifference hp
  have hTPos : 0 < T := by linarith
  have hImPos :
      0 < abs (symmetricCompletedZeroValue p).im :=
    hTPos.trans_le hBounds.1
  have hKernel :=
    norm_centered_cpow_kernel_horizontal_le
      x hx hpReLine hImPos
  have hNumerator : 0 <= 4 * (x : Real) := by positivity
  have hDenominator :
      4 * (x : Real) / abs (symmetricCompletedZeroValue p).im <=
        4 * (x : Real) / T :=
    div_le_div_of_nonneg_left hNumerator hTPos hBounds.1
  exact hKernel.trans hDenominator

end BombieriVinogradov.SiegelWalfisz
