import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions

/-!
# Exceptional zero values

This module packages the selected exceptional zero and its functional-equation
reflection as a finite value set, disjoint from the retained-zero predicate.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The selected exceptional zero and its reflection, or the empty set when no
exceptional zero is selected. -/
def exceptionalZeroValues : Option Complex -> Finset Complex
  | none => {}
  | some beta => {beta, 1 - beta}

/-- Membership in the exceptional pair is exactly failure of the retained-zero
predicate. -/
@[simp] theorem mem_exceptionalZeroValues_iff
    {exceptional : Option Complex} {rho : Complex} :
    Membership.mem (exceptionalZeroValues exceptional) rho <->
      Not (IsRetainedZero exceptional rho) := by
  cases exceptional with
  | none =>
    simp [exceptionalZeroValues, IsRetainedZero]
  | some beta =>
    simp only [exceptionalZeroValues, Finset.mem_insert,
      Finset.mem_singleton, IsRetainedZero]
    tauto

/-- The retained-zero predicate is exactly exclusion from the exceptional
pair. -/
@[simp] theorem isRetainedZero_iff_not_mem_exceptionalZeroValues
    {exceptional : Option Complex} {rho : Complex} :
    IsRetainedZero exceptional rho <->
      Not (Membership.mem (exceptionalZeroValues exceptional) rho) := by
  rw [mem_exceptionalZeroValues_iff]
  simp

end BombieriVinogradov.SiegelWalfisz
