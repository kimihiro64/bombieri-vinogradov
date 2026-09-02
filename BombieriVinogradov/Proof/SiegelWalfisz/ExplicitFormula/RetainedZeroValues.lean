import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions

/-!
# Retained critical-strip zero values

This module owns the multiplicity-index and deduplicated value finsets used by
the primed zero sum, together with its direct finite-sum presentation.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace BombieriVinogradov.SiegelWalfisz

/-- Multiplicity indices retained by the primed zero sum. -/
def retainedCriticalZeroIndices {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (T : Real)
    (exceptional : Option Complex) : Finset (SymmetricCompletedZeroIndex chi) := by
  classical
  exact (criticalStripZeroTruncation chi T).filter fun p =>
    IsRetainedZero exceptional (Complex.Hadamard.divisorZeroIndex₀_val p)

/-- Distinct complex values represented by the retained multiplicity indices. -/
def retainedCriticalZeroValues {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (T : Real)
    (exceptional : Option Complex) : Finset Complex := by
  classical
  exact (retainedCriticalZeroIndices chi T exceptional).image
    Complex.Hadamard.divisorZeroIndex₀_val

@[simp] theorem mem_retainedCriticalZeroIndices_iff
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex}
    {p : SymmetricCompletedZeroIndex chi} :
    p ∈ retainedCriticalZeroIndices chi T exceptional ↔
      p ∈ criticalStripZeroTruncation chi T ∧
        IsRetainedZero exceptional (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  simp [retainedCriticalZeroIndices]

theorem ne_zero_of_mem_retainedCriticalZeroValues
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex} {rho : Complex}
    (hrho : rho ∈ retainedCriticalZeroValues chi T exceptional) : Ne rho 0 := by
  classical
  have hWitness := Finset.mem_image.mp hrho
  let p := hWitness.choose
  have hpValue : Complex.Hadamard.divisorZeroIndex₀_val p = rho :=
    hWitness.choose_spec.2
  intro hrhoZero
  exact Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    (hpValue.trans hrhoZero)

theorem truncatedCriticalZeroSum_eq_sum_retainedCriticalZeroIndices
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (T : Real) (exceptional : Option Complex) :
    truncatedCriticalZeroSum chi x T exceptional =
      ∑ p ∈ retainedCriticalZeroIndices chi T exceptional,
        (x : Complex) ^ (Complex.Hadamard.divisorZeroIndex₀_val p) /
          Complex.Hadamard.divisorZeroIndex₀_val p := by
  rfl

end BombieriVinogradov.SiegelWalfisz
