import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValuesNonzero
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.CandidateValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedExceptionalDisjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite residue-candidate sum decomposition

This module decomposes the candidate-value sum into the origin, retained
critical-zero values, and the exceptional reflected pair.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Summing over all residue candidates is the sum of the three disjoint
candidate sources. -/
theorem sum_explicitFormulaResidueCandidateValues
    {N : Nat} [NeZero N] {c : Real}
    {chi : DirichletCharacter Complex N} {T : Real}
    {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    (f : Complex -> Complex) :
    Finset.sum (explicitFormulaResidueCandidateValues chi T exceptional) f =
      f 0 +
        (Finset.sum (retainedCriticalZeroValues chi T exceptional) f +
          Finset.sum (exceptionalZeroValues exceptional) f) := by
  classical
  have hZeroNotUnion : Not (Membership.mem
      (Union.union (retainedCriticalZeroValues chi T exceptional)
        (exceptionalZeroValues exceptional)) 0) := by
    intro hZero
    exact Or.elim (Finset.mem_union.mp hZero)
      (fun hRetained =>
        ne_zero_of_mem_retainedCriticalZeroValues hRetained rfl)
      (fun hExceptional =>
        ne_zero_of_mem_exceptionalZeroValues hChoice hExceptional rfl)
  unfold explicitFormulaResidueCandidateValues
  rw [Finset.sum_insert hZeroNotUnion]
  rw [Finset.sum_union
    (disjoint_retainedCriticalZeroValues_exceptionalZeroValues
      chi T exceptional)]

end BombieriVinogradov.SiegelWalfisz
