import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Centered explicit-formula broken boundary

This module centers the finite broken-boundary integral at x equals one while
keeping the same rectangle.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered broken boundary is its x-value minus its value at one. -/
def centeredExplicitFormulaBrokenBoundaryIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (U c T : Real) : Complex :=
  explicitFormulaBrokenBoundaryIntegral (explicitFormulaIntegrand chi x) U c T -
    explicitFormulaBrokenBoundaryIntegral (explicitFormulaIntegrand chi 1) U c T

/-- Centering makes the broken-boundary integral vanish at one. -/
theorem centeredExplicitFormulaBrokenBoundaryIntegral_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (U c T : Real) :
    centeredExplicitFormulaBrokenBoundaryIntegral chi 1 U c T = 0 := by
  simp [centeredExplicitFormulaBrokenBoundaryIntegral]

end BombieriVinogradov.SiegelWalfisz
