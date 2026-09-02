import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Mathlib.Data.Finset.Disjoint

/-!
# Retained and exceptional zero values are disjoint

This module extracts the retained predicate from the image finset and proves
that retained zero values do not overlap the exceptional reflected pair.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every value represented in the retained critical-zero finset satisfies
the retained-zero predicate. -/
theorem isRetainedZero_of_mem_retainedCriticalZeroValues
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex} {rho : Complex}
    (hrho : Membership.mem
      (retainedCriticalZeroValues chi T exceptional) rho) :
    IsRetainedZero exceptional rho := by
  have hWitness := Finset.mem_image.mp hrho
  have hValue := hWitness.choose_spec.2
  have hRetained :=
    (mem_retainedCriticalZeroIndices_iff.mp hWitness.choose_spec.1).2
  rw [hValue] at hRetained
  exact hRetained

/-- Retained critical-zero values are disjoint from the exceptional pair. -/
theorem disjoint_retainedCriticalZeroValues_exceptionalZeroValues
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (T : Real) (exceptional : Option Complex) :
    Disjoint (retainedCriticalZeroValues chi T exceptional)
      (exceptionalZeroValues exceptional) := by
  rw [Finset.disjoint_left]
  intro rho hRetained hExceptional
  exact (mem_exceptionalZeroValues_iff.mp hExceptional)
    (isRetainedZero_of_mem_retainedCriticalZeroValues hRetained)

end BombieriVinogradov.SiegelWalfisz
