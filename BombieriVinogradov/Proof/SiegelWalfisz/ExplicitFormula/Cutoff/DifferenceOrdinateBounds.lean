import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.DifferenceIndices
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue

/-!
# Ordinates of newly retained zeros

This module extracts the exact old/new absolute-ordinate bounds from membership
in the retained cutoff-difference finset.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem abs_im_bounds_of_mem_retainedCriticalZeroCutoffDifference
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T Tprime : Real} {exceptional : Option Complex}
    {p : SymmetricCompletedZeroIndex chi}
    (hp :
      (retainedCriticalZeroCutoffDifference chi T Tprime exceptional :
        Set (SymmetricCompletedZeroIndex chi)) p) :
    And
      (T <= abs (symmetricCompletedZeroValue p).im)
      (abs (symmetricCompletedZeroValue p).im < Tprime) := by
  have hpDifference :=
    mem_retainedCriticalZeroCutoffDifference_iff.mp hp
  have hpLarge := mem_retainedCriticalZeroIndices_iff.mp hpDifference.1
  have hpStrip := mem_criticalStripZeroTruncation_iff.mp hpLarge.1
  have hpStripASCII :
      And
        (0 < (symmetricCompletedZeroValue p).re)
        (And
          ((symmetricCompletedZeroValue p).re < 1)
          (abs (symmetricCompletedZeroValue p).im < Tprime)) := by
    simpa [symmetricCompletedZeroValue] using hpStrip
  have hLower : T <= abs (symmetricCompletedZeroValue p).im := by
    apply le_of_not_gt
    intro hBelow
    apply hpDifference.2
    have hCriticalSmall :=
      (mem_criticalStripZeroTruncation_iff
        (chi := chi) (T := T) (p := p)).mpr (by
          simpa [symmetricCompletedZeroValue] using
            And.intro hpStripASCII.1
              (And.intro hpStripASCII.2.1 hBelow))
    have hRetainedSmall :=
      (mem_retainedCriticalZeroIndices_iff
        (chi := chi) (T := T) (exceptional := exceptional) (p := p)).mpr
          (And.intro hCriticalSmall hpLarge.2)
    exact hRetainedSmall
  exact And.intro hLower hpStripASCII.2.2

end BombieriVinogradov.SiegelWalfisz
