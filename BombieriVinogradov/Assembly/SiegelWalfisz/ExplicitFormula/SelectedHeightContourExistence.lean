import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.FixedHeightContourDecomposition
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.HorizontalBoundaryBoundsAtHeight
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightContourData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.GoodTwoSidedHeightLogDerivativeBound
import Mathlib.Tactic.Linarith

/-!
# Existence of selected-height centered contour data

This module makes one good-height choice and constructs the contour identity
and both horizontal estimates at that exact same height.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_selectedHeightContourData :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall x : Nat, 2 < x ->
              forall T : Real, 2 <= T ->
                forall c0 : Real, forall exceptional : Option Complex,
                  IsExceptionalZeroChoice c0 chi exceptional ->
                    Nonempty
                      (SelectedHeightContourData chi x T C exceptional)) := by
  choose C hCPos hGood using
    exists_goodTwoSidedHeight_logDeriv_LFunction_le_sq
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive x hx T hT c0 exceptional hChoice
  choose Tprime hTprimeLower hTprimeUpper hTop hBottom using
    hGood hN hchi hPrimitive T hT
  have hTprimePos : 0 < Tprime := by
    linarith
  have hIdentity :=
    centeredExplicitFormulaVerticalIntegral_eq_decomposed_optimized
      hchi hPrimitive hx hTprimePos c0 exceptional hChoice
        (fun hs hLower hUpper => (hTop hs hLower hUpper).1)
        (fun hs hLower hUpper => (hBottom hs hLower hUpper).1)
  have hBounds :=
    centeredHorizontalBoundary_bounds_of_LFunction_data
      hchi hx hTprimePos hTop hBottom
  exact Nonempty.intro {
    height := Tprime
    height_lower := hTprimeLower
    height_upper := hTprimeUpper
    contour_identity := hIdentity
    top_bound := hBounds.1
    bottom_bound := hBounds.2
  }

end BombieriVinogradov.SiegelWalfisz
