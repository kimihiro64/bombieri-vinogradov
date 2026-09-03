import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightContourData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Ring

/-!
# Centered explicit-formula residual bound

This module combines a fixed contour identity with supplied Perron and
full-boundary estimates by exact algebra and the norm triangle inequality.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_centeredFormulaResidual_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {x : Nat} {T C : Real} {exceptional : Option Complex}
    (data : SelectedHeightContourData chi x T C exceptional)
    {P B : Real}
    (hPerron :
      norm (centeredExplicitFormulaVerticalIntegral chi x
        (optimizedPerronLine x) data.height -
          characterChebyshevHalfSum x chi) <= P)
    (hBoundary :
      norm
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) data.height +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height) <= B) :
    norm
        (characterChebyshevHalfSum x chi +
          (lFunctionOriginMultiplicity chi : Complex) *
            Complex.log (x : Complex) +
          centeredTruncatedCriticalZeroSum chi x data.height exceptional -
          centeredExceptionalResidueSum chi x exceptional) <=
      P + B := by
  have hIdentity :
      characterChebyshevHalfSum x chi +
          (lFunctionOriginMultiplicity chi : Complex) *
            Complex.log (x : Complex) +
          centeredTruncatedCriticalZeroSum chi x data.height exceptional -
          centeredExceptionalResidueSum chi x exceptional =
        -(centeredExplicitFormulaVerticalIntegral chi x
            (optimizedPerronLine x) data.height -
          characterChebyshevHalfSum x chi) +
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) data.height +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height) := by
    rw [data.contour_identity]
    ring
  rw [hIdentity]
  calc
    norm
        (-(centeredExplicitFormulaVerticalIntegral chi x
            (optimizedPerronLine x) data.height -
          characterChebyshevHalfSum x chi) +
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) data.height +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height)) <=
      norm (-(centeredExplicitFormulaVerticalIntegral chi x
          (optimizedPerronLine x) data.height -
        characterChebyshevHalfSum x chi)) +
      norm
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) data.height +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height) :=
      norm_add_le _ _
    _ =
      norm (centeredExplicitFormulaVerticalIntegral chi x
          (optimizedPerronLine x) data.height -
        characterChebyshevHalfSum x chi) +
      norm
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) data.height +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height) := by
      rw [norm_neg]
    _ <= P + B := add_le_add hPerron hBoundary

end BombieriVinogradov.SiegelWalfisz
