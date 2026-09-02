import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedResidueAwayZero
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ZeroResidue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticLFunctionReflection
import Mathlib.Analysis.Analytic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Pointwise exceptional residues

This module computes the regularized explicit-formula residues at a simple
exceptional zero and its functional-equation reflection.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The regularized residue at a simple exceptional zero is its negative complex-power term. -/
theorem residue_regularizedExplicitFormulaIntegrand_exceptionalZero
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hx : 0 < x) {c : Real} {beta : Complex}
    (hExceptional : IsExceptionalZero c chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1) :
    residue (regularizedExplicitFormulaIntegrand chi x) beta =
      -((x : Complex) ^ beta / beta) := by
  have hBetaNe : Ne beta 0 := by
    intro hBetaZero
    have hReZero : beta.re = 0 := by
      simpa using congrArg Complex.re hBetaZero
    linarith [hExceptional.2.2.1]
  calc
    residue (regularizedExplicitFormulaIntegrand chi x) beta =
        residue (explicitFormulaIntegrand chi x) beta :=
      residue_regularizedExplicitFormulaIntegrand_eq_of_ne_zero
        hchi x hx hBetaNe
    _ = -((analyticOrderNatAt chi.LFunction beta : Nat) : Complex) *
          ((x : Complex) ^ beta / beta) :=
      residue_explicitFormulaIntegrand hchi hx hBetaNe
    _ = -((x : Complex) ^ beta / beta) := by
      rw [hSimple]
      norm_num

/-- The regularized residue at the reflected simple quadratic zero is its negative complex-power term. -/
theorem residue_regularizedExplicitFormulaIntegrand_exceptionalReflection
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) (hx : 0 < x) {c : Real} {beta : Complex}
    (hExceptional : IsExceptionalZero c chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1) :
    residue (regularizedExplicitFormulaIntegrand chi x) (1 - beta) =
      -((x : Complex) ^ (1 - beta) / (1 - beta)) := by
  have hBetaPos : 0 < beta.re := hExceptional.2.2.1
  have hBetaLt : beta.re < 1 := hExceptional.2.2.2.1
  have hReflectNe : Ne (1 - beta) 0 := by
    intro hReflectZero
    have hReZero : (1 - beta).re = 0 := by
      simpa using congrArg Complex.re hReflectZero
    change 1 - beta.re = 0 at hReZero
    linarith
  have hReflectSimple :
      analyticOrderNatAt chi.LFunction (1 - beta) = 1 :=
    (analyticOrderNatAt_LFunction_one_sub_of_quadratic
      hchi hPrimitive hSquare hBetaPos hBetaLt).trans hSimple
  calc
    residue (regularizedExplicitFormulaIntegrand chi x) (1 - beta) =
        residue (explicitFormulaIntegrand chi x) (1 - beta) :=
      residue_regularizedExplicitFormulaIntegrand_eq_of_ne_zero
        hchi x hx hReflectNe
    _ = -((analyticOrderNatAt chi.LFunction (1 - beta) : Nat) : Complex) *
          ((x : Complex) ^ (1 - beta) / (1 - beta)) :=
      residue_explicitFormulaIntegrand hchi hx hReflectNe
    _ = -((x : Complex) ^ (1 - beta) / (1 - beta)) := by
      rw [hReflectSimple]
      norm_num

end BombieriVinogradov.SiegelWalfisz
