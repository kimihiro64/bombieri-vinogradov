import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.BottomBoundaryIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.LeftBoundaryIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.TopBoundaryIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.VerticalIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Selected-height centered contour data

This module defines the fixed-witness interface joining a decomposed contour
identity to the exact top and bottom boundary estimates at one selected height.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

structure SelectedHeightContourData
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (T C : Real) (exceptional : Option Complex) where
  height : Real
  height_lower : T <= height
  height_upper : height <= T + 1
  contour_identity :
    centeredExplicitFormulaVerticalIntegral chi x
        (optimizedPerronLine x) height =
      (-(lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex) +
        (-centeredTruncatedCriticalZeroSum chi x height exceptional +
          centeredExceptionalResidueSum chi x exceptional)) +
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) height +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) height +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) height)
  top_bound :
    norm (centeredExplicitFormulaTopBoundaryIntegral chi x
        ((1 : Real) / 2) (optimizedPerronLine x) height) <=
      (1 / (2 * Real.pi)) *
        ((C * (zeroHeightLogScale N T) ^ 2) *
          (4 * (x : Real) / abs height) *
            abs (optimizedPerronLine x - (-(1 : Real) / 2)))
  bottom_bound :
    norm (centeredExplicitFormulaBottomBoundaryIntegral chi x
        ((1 : Real) / 2) (optimizedPerronLine x) height) <=
      (1 / (2 * Real.pi)) *
        ((C * (zeroHeightLogScale N T) ^ 2) *
          (4 * (x : Real) / abs (-height)) *
            abs ((-(1 : Real) / 2) - optimizedPerronLine x))

end BombieriVinogradov.SiegelWalfisz
