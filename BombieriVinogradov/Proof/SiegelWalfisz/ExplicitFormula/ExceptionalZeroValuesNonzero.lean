import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues

/-!
# Nonvanishing of exceptional zero values

This module records that a selected exceptional zero and its reflection are
both nonzero because both lie strictly inside the critical strip.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every value in a faithfully selected exceptional pair is nonzero. -/
theorem ne_zero_of_mem_exceptionalZeroValues
    {N : Nat} [NeZero N] {c : Real}
    {chi : DirichletCharacter Complex N} {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    {rho : Complex}
    (hrho : Membership.mem (exceptionalZeroValues exceptional) rho) :
    Ne rho 0 := by
  cases exceptional with
  | none =>
    simp [exceptionalZeroValues] at hrho
  | some beta =>
    change IsExceptionalZero c chi beta at hChoice
    simp only [exceptionalZeroValues, Finset.mem_insert,
      Finset.mem_singleton] at hrho
    exact Or.elim hrho
      (fun hrhoBeta => by
        subst rho
        intro hbetaZero
        have hReZero : beta.re = 0 := by
          simpa using congrArg Complex.re hbetaZero
        linarith [hChoice.2.2.1])
      (fun hrhoReflect => by
        subst rho
        intro hReflectZero
        have hReZero : (1 - beta).re = 0 := by
          simpa using congrArg Complex.re hReflectZero
        change 1 - beta.re = 0 at hReZero
        linarith [hChoice.2.2.2.1])

end BombieriVinogradov.SiegelWalfisz
