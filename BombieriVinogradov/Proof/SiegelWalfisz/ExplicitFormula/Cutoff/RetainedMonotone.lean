import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Mathlib.Data.Finset.Basic

/-!
# Retained zero cutoff monotonicity

This module proves that enlarging the strict ordinate cutoff preserves every
critical-strip multiplicity index and its exceptional-zero retention status.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem criticalStripZeroTruncation_mono
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T Tprime : Real} (hCutoff : T <= Tprime) :
    criticalStripZeroTruncation chi T <=
      criticalStripZeroTruncation chi Tprime := by
  intro p hp
  rw [mem_criticalStripZeroTruncation_iff] at hp
  rw [mem_criticalStripZeroTruncation_iff]
  exact And.intro hp.1
    (And.intro hp.2.1 (lt_of_lt_of_le hp.2.2 hCutoff))

theorem retainedCriticalZeroIndices_mono
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T Tprime : Real} (hCutoff : T <= Tprime)
    (exceptional : Option Complex) :
    retainedCriticalZeroIndices chi T exceptional <=
      retainedCriticalZeroIndices chi Tprime exceptional := by
  intro p hp
  rw [mem_retainedCriticalZeroIndices_iff] at hp
  rw [mem_retainedCriticalZeroIndices_iff]
  exact And.intro (criticalStripZeroTruncation_mono hCutoff hp.1) hp.2

end BombieriVinogradov.SiegelWalfisz
