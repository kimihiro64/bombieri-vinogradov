import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Retained values as a restriction of the unexcluded truncation

An excluded pair removes complex values without changing the index or
multiplicity of any remaining zero.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem mem_retainedCriticalZeroValues_iff_unexcluded_and_retained
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (T : Real) (e : Option Complex) (rho : Complex) :
    (retainedCriticalZeroValues chi T e : Set Complex) rho <->
      And ((retainedCriticalZeroValues chi T none : Set Complex) rho)
        (IsRetainedZero e rho) := by
  classical
  have hForward : (retainedCriticalZeroValues chi T e : Set Complex) rho ->
      And ((retainedCriticalZeroValues chi T none : Set Complex) rho)
        (IsRetainedZero e rho) := by
    intro h
    have hWitness := Finset.mem_image.mp h
    let p : SymmetricCompletedZeroIndex chi := hWitness.choose
    have hp : (retainedCriticalZeroIndices chi T e :
        Set (SymmetricCompletedZeroIndex chi)) p := hWitness.choose_spec.1
    have hValue : symmetricCompletedZeroValue p = rho := hWitness.choose_spec.2
    have hParts := mem_retainedCriticalZeroIndices_iff.mp hp
    have hpNone : (retainedCriticalZeroIndices chi T none :
        Set (SymmetricCompletedZeroIndex chi)) p :=
      mem_retainedCriticalZeroIndices_iff.mpr (And.intro hParts.1 True.intro)
    have hNone : (retainedCriticalZeroValues chi T none : Set Complex) rho :=
      Finset.mem_image.mpr (Exists.intro p (And.intro hpNone hValue))
    have hKept : IsRetainedZero e rho := by
      rw [<- hValue]
      exact hParts.2
    exact And.intro hNone hKept
  have hBackward : And ((retainedCriticalZeroValues chi T none : Set Complex) rho)
      (IsRetainedZero e rho) -> (retainedCriticalZeroValues chi T e : Set Complex) rho := by
    intro h
    have hWitness := Finset.mem_image.mp h.1
    let p : SymmetricCompletedZeroIndex chi := hWitness.choose
    have hp : (retainedCriticalZeroIndices chi T none :
        Set (SymmetricCompletedZeroIndex chi)) p := hWitness.choose_spec.1
    have hValue : symmetricCompletedZeroValue p = rho := hWitness.choose_spec.2
    have hParts := mem_retainedCriticalZeroIndices_iff.mp hp
    have hKept : IsRetainedZero e (symmetricCompletedZeroValue p) := by
      rw [hValue]
      exact h.2
    have hpKept : (retainedCriticalZeroIndices chi T e :
        Set (SymmetricCompletedZeroIndex chi)) p :=
      mem_retainedCriticalZeroIndices_iff.mpr (And.intro hParts.1 hKept)
    exact Finset.mem_image.mpr (Exists.intro p (And.intro hpKept hValue))
  exact Iff.intro hForward hBackward

end BombieriVinogradov.SiegelWalfisz
