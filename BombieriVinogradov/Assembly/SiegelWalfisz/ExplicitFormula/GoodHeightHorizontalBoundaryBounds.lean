import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.HorizontalBoundaryBoundsAtHeight
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.GoodTwoSidedHeightLogDerivativeBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Centered horizontal-boundary bounds at a common good height

This module applies the common positive-and-negative horizontal-line data to
the separately verified top and bottom centered integral estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_goodHeight_centeredHorizontalBoundary_bounds :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall x : Nat, 2 < x ->
              forall T : Real, 2 <= T ->
                exists Tprime : Real, And (T <= Tprime)
                  (And (Tprime <= T + 1)
                    (And
                      (norm (centeredExplicitFormulaTopBoundaryIntegral
                          chi x ((1 : Real) / 2)
                            (optimizedPerronLine x) Tprime) <=
                        (1 / (2 * Real.pi)) *
                          ((C * (zeroHeightLogScale N T) ^ 2) *
                            (4 * (x : Real) / abs Tprime) *
                              abs (optimizedPerronLine x -
                                (-(1 : Real) / 2))))
                      (norm (centeredExplicitFormulaBottomBoundaryIntegral
                          chi x ((1 : Real) / 2)
                            (optimizedPerronLine x) Tprime) <=
                        (1 / (2 * Real.pi)) *
                          ((C * (zeroHeightLogScale N T) ^ 2) *
                            (4 * (x : Real) / abs (-Tprime)) *
                              abs ((-(1 : Real) / 2) -
                                optimizedPerronLine x)))))) := by
  choose C hCPos hGood using
    exists_goodTwoSidedHeight_logDeriv_LFunction_le_sq
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive x hx T hT
  choose Tprime hTprimeLower hTprimeUpper hTop hBottom using
    hGood hN hchi hPrimitive T hT
  have hTprimePos : 0 < Tprime := by
    linarith
  have hBounds :=
    centeredHorizontalBoundary_bounds_of_LFunction_data
      hchi hx hTprimePos hTop hBottom
  exact Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper hBounds))

end BombieriVinogradov.SiegelWalfisz
