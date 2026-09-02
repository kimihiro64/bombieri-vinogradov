import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.KernelDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions

/-!
# Scaled regularized integrand identity

This module isolates the exact punctured algebra used to compute the
regularized integrand's residue at the origin.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Away from zero, scaling the regularized integrand separates the finite
logarithmic-derivative remainder and complex-power difference quotient. -/
theorem mul_regularizedExplicitFormulaIntegrand_eq_of_ne_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) {s : Complex} (hs : Ne s 0) :
    s * regularizedExplicitFormulaIntegrand chi x s =
      -((x : Complex) ^ s * lFunctionOriginLogDerivativeRemainder chi s) -
        (lFunctionOriginMultiplicity chi : Complex) *
          originCpowDifferenceQuotient x s := by
  unfold regularizedExplicitFormulaIntegrand originDoublePoleCorrection
    lFunctionOriginLogDerivativeRemainder originCpowDifferenceQuotient
    explicitFormulaIntegrand
  field_simp
  ring

end BombieriVinogradov.SiegelWalfisz
