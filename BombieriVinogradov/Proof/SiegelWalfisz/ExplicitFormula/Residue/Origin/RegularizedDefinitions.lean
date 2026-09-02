import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions

/-!
# Double-pole regularization data at the origin

This module owns only the explicit double-pole correction and the corrected
explicit-formula integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The term that cancels the possible origin double pole. -/
def originDoublePoleCorrection
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (s : Complex) : Complex :=
  (lFunctionOriginMultiplicity chi : Complex) / s ^ 2

/-- The explicit-formula integrand after cancelling its possible origin
double pole. -/
def regularizedExplicitFormulaIntegrand
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (s : Complex) : Complex :=
  explicitFormulaIntegrand chi x s + originDoublePoleCorrection chi s

end BombieriVinogradov.SiegelWalfisz
