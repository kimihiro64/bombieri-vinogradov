import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues

/-!
# Retained zero cutoff-difference indices

This module names the finite multiplicity-index set present at the larger
cutoff and absent at the smaller cutoff.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def retainedCriticalZeroCutoffDifference
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (T Tprime : Real) (exceptional : Option Complex) :
    Finset (SymmetricCompletedZeroIndex chi) := by
  classical
  exact (retainedCriticalZeroIndices chi Tprime exceptional).filter fun p =>
    Not ((retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p)

@[simp] theorem mem_retainedCriticalZeroCutoffDifference_iff
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T Tprime : Real} {exceptional : Option Complex}
    {p : SymmetricCompletedZeroIndex chi} :
    (retainedCriticalZeroCutoffDifference chi T Tprime exceptional :
        Set (SymmetricCompletedZeroIndex chi)) p <->
      And
        ((retainedCriticalZeroIndices chi Tprime exceptional :
          Set (SymmetricCompletedZeroIndex chi)) p)
        (Not ((retainedCriticalZeroIndices chi T exceptional :
          Set (SymmetricCompletedZeroIndex chi)) p)) := by
  classical
  unfold retainedCriticalZeroCutoffDifference
  have hForward :
      ((retainedCriticalZeroIndices chi Tprime exceptional).filter
          (fun q => Not ((retainedCriticalZeroIndices chi T exceptional :
            Set (SymmetricCompletedZeroIndex chi)) q)) :
        Set (SymmetricCompletedZeroIndex chi)) p ->
        And
          ((retainedCriticalZeroIndices chi Tprime exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p)
          (Not ((retainedCriticalZeroIndices chi T exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p)) :=
    fun hp => Finset.mem_filter.mp hp
  have hBackward :
      And
          ((retainedCriticalZeroIndices chi Tprime exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p)
          (Not ((retainedCriticalZeroIndices chi T exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p)) ->
        ((retainedCriticalZeroIndices chi Tprime exceptional).filter
          (fun q => Not ((retainedCriticalZeroIndices chi T exceptional :
            Set (SymmetricCompletedZeroIndex chi)) q)) :
          Set (SymmetricCompletedZeroIndex chi)) p :=
    fun hp => Finset.mem_filter.mpr hp
  exact Iff.intro hForward hBackward

end BombieriVinogradov.SiegelWalfisz
