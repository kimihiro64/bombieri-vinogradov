import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered top contour integral

This module isolates the top horizontal segment of the centered contour.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Difference of the top horizontal integrals at x and at one. -/
def centeredExplicitFormulaTopBoundaryIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (U c T : Real) : Complex :=
  HIntegral' (explicitFormulaIntegrand chi x) (-U) c T -
    HIntegral' (explicitFormulaIntegrand chi 1) (-U) c T

/-- The centered top integral vanishes at one. -/
theorem centeredExplicitFormulaTopBoundaryIntegral_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (U c T : Real) :
    centeredExplicitFormulaTopBoundaryIntegral chi 1 U c T = 0 := by
  simp [centeredExplicitFormulaTopBoundaryIntegral]

end BombieriVinogradov.SiegelWalfisz
