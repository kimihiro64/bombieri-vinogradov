import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Centered truncated zero sum

This module centers the retained critical-zero sum at x equals one, keeping the
Unicode-only divisor implementation behind the existing compiled interface.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered retained-zero contribution is the x-value minus its value at one. -/
def centeredTruncatedCriticalZeroSum {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Nat) (T : Real)
    (exceptional : Option Complex) : Complex :=
  truncatedCriticalZeroSum chi x T exceptional -
    truncatedCriticalZeroSum chi 1 T exceptional

/-- Centering makes the retained critical-zero contribution vanish at one. -/
theorem centeredTruncatedCriticalZeroSum_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (T : Real) (exceptional : Option Complex) :
    centeredTruncatedCriticalZeroSum chi 1 T exceptional = 0 := by
  simp [centeredTruncatedCriticalZeroSum]

end BombieriVinogradov.SiegelWalfisz
