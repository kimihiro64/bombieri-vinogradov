import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.RetainedZeroReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroDivisorReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith

/-!
# Retained multiplicity-index reflection
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedZeroReflection_mem_retainedCriticalZeroIndices
    {c : Real} {N : Nat} [NeZero N]
    {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    {T : Real} {p : SymmetricCompletedZeroIndex chi}
    (hp : (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi))
        (symmetricCompletedZeroReflection hchi hPrimitive p) := by
  have hpData :=
    (mem_retainedCriticalZeroIndices_iff (p := p)).mp hp
  have hpStrip :
      And (0 < (symmetricCompletedZeroValue p).re)
        (And ((symmetricCompletedZeroValue p).re < 1)
          (abs (symmetricCompletedZeroValue p).im < T)) := by
    simpa [symmetricCompletedZeroValue] using
      (mem_criticalStripZeroTruncation_iff.mp hpData.1)
  have hpRetained :
      IsRetainedZero exceptional (symmetricCompletedZeroValue p) := by
    simpa [symmetricCompletedZeroValue] using hpData.2
  have hReflectedValue :
      symmetricCompletedZeroValue
          (symmetricCompletedZeroReflection hchi hPrimitive p) =
        1 - (starRingEnd Complex) (symmetricCompletedZeroValue p) := by
    exact symmetricCompletedZeroReflection_val hchi hPrimitive p
  have hReflectedRe :
      (1 - (starRingEnd Complex)
        (symmetricCompletedZeroValue p)).re =
          1 - (symmetricCompletedZeroValue p).re := by
    simp
  have hReflectedIm :
      (1 - (starRingEnd Complex)
        (symmetricCompletedZeroValue p)).im =
          (symmetricCompletedZeroValue p).im := by
    simp
  have hReflectedStrip :
      And
        (0 < (symmetricCompletedZeroValue
          (symmetricCompletedZeroReflection hchi hPrimitive p)).re)
        (And
          ((symmetricCompletedZeroValue
            (symmetricCompletedZeroReflection hchi hPrimitive p)).re < 1)
          (abs (symmetricCompletedZeroValue
            (symmetricCompletedZeroReflection hchi hPrimitive p)).im < T)) := by
    rw [hReflectedValue, hReflectedRe, hReflectedIm]
    exact And.intro (by linarith [hpStrip.2.1])
      (And.intro (by linarith [hpStrip.1]) hpStrip.2.2)
  have hReflectedRetained :
      IsRetainedZero exceptional
        (symmetricCompletedZeroValue
          (symmetricCompletedZeroReflection hchi hPrimitive p)) := by
    rw [hReflectedValue]
    exact isRetainedZero_one_sub_conj hChoice hpRetained
  have hCriticalMembership :
      (criticalStripZeroTruncation chi T :
        Set (SymmetricCompletedZeroIndex chi))
          (symmetricCompletedZeroReflection hchi hPrimitive p) :=
    (mem_criticalStripZeroTruncation_iff
      (p := symmetricCompletedZeroReflection hchi hPrimitive p)).mpr
        (by simpa [symmetricCompletedZeroValue] using hReflectedStrip)
  exact (mem_retainedCriticalZeroIndices_iff
    (p := symmetricCompletedZeroReflection hchi hPrimitive p)).mpr
      (And.intro hCriticalMembership
        (by simpa [symmetricCompletedZeroValue] using
          hReflectedRetained))

end BombieriVinogradov.SiegelWalfisz
