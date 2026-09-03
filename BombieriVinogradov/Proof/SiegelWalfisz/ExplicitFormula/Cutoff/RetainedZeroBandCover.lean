import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Covering retained zeros by absolute-ordinate bands
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def retainedCriticalZeroBandIndex
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (p : SymmetricCompletedZeroIndex chi) : Nat :=
  Nat.floor (abs (symmetricCompletedZeroValue p).im)

theorem mem_retainedCriticalZeroBand_bandIndex
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex}
    {p : SymmetricCompletedZeroIndex chi}
    (hp : (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    (retainedCriticalZeroBand chi T exceptional
      (retainedCriticalZeroBandIndex p) :
        Set (SymmetricCompletedZeroIndex chi)) p := by
  apply mem_retainedCriticalZeroBand_iff.mpr
  have hLower :
      ((Nat.floor (abs (symmetricCompletedZeroValue p).im) : Nat) : Real) <=
        abs (symmetricCompletedZeroValue p).im :=
    Nat.floor_le (abs_nonneg (symmetricCompletedZeroValue p).im)
  have hUpper :
      abs (symmetricCompletedZeroValue p).im <
        ((Nat.floor (abs (symmetricCompletedZeroValue p).im) : Nat) : Real) +
          1 :=
    Nat.lt_floor_add_one _
  exact And.intro hp
    (And.intro
      (by simpa [retainedCriticalZeroBandIndex] using hLower)
      (by simpa [retainedCriticalZeroBandIndex] using hUpper))

theorem retainedCriticalZeroBandIndex_lt_ceil
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} (hT : 0 < T) {exceptional : Option Complex}
    {p : SymmetricCompletedZeroIndex chi}
    (hp : (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    retainedCriticalZeroBandIndex p < Nat.ceil T := by
  have hpData :=
    (mem_retainedCriticalZeroIndices_iff (p := p)).mp hp
  have hpStrip :=
    mem_criticalStripZeroTruncation_iff.mp hpData.1
  have hHeight :
      abs (symmetricCompletedZeroValue p).im < T := by
    simpa [symmetricCompletedZeroValue] using hpStrip.2.2
  simpa [retainedCriticalZeroBandIndex] using
    Nat.floor_lt_ceil_of_lt_of_pos hHeight hT

end BombieriVinogradov.SiegelWalfisz
