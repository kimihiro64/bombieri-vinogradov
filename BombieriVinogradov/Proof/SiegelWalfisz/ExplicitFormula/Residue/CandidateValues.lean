import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues

/-!
# Explicit-formula residue candidate values

This module packages the three finite sources of regularized contour residues:
the origin, retained critical-strip zeros, and the possible exceptional pair.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Finite values that can contribute a residue inside the explicit-formula
contour. -/
def explicitFormulaResidueCandidateValues {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (T : Real)
    (exceptional : Option Complex) : Finset Complex :=
  insert 0
    (Union.union (retainedCriticalZeroValues chi T exceptional)
      (exceptionalZeroValues exceptional))

/-- Membership in the residue candidate set splits into the origin, a retained
critical zero, or an exceptional-pair value. -/
@[simp] theorem mem_explicitFormulaResidueCandidateValues_iff
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex} {rho : Complex} :
    Membership.mem
        (explicitFormulaResidueCandidateValues chi T exceptional) rho <->
      Or (rho = 0)
        (Or
          (Membership.mem (retainedCriticalZeroValues chi T exceptional) rho)
          (Membership.mem (exceptionalZeroValues exceptional) rho)) := by
  simp only [explicitFormulaResidueCandidateValues, Finset.mem_insert,
    Finset.mem_union]

end BombieriVinogradov.SiegelWalfisz
