import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.CenteredFormulaResidualBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightBoundarySourceScale
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightContourExistence
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightResidualData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.CenteredPerron
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selected-height centered residual in the source scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_selectedHeightResidualData_sourceScale :
    exists CHeight CResidual : Real,
      And (0 < CHeight) (And (0 < CResidual)
        (forall {N : Nat} [NeZero N], 3 <= N ->
          forall {chi : DirichletCharacter Complex N},
            Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
              forall {x : Nat}, 2 < x ->
                forall {T : Real}, 2 <= T -> T <= x ->
                  forall {c0 : Real} {exceptional : Option Complex},
                    IsExceptionalZeroChoice c0 chi exceptional ->
                      Nonempty
                        (SelectedHeightResidualData chi x T
                          CHeight CResidual exceptional))) := by
  choose CHeight hCHeightPos hData using
    exists_selectedHeightContourData
  choose CLeft hCLeftPos hBoundary using
    exists_norm_selectedHeight_boundary_sum_le_sourceScale
  choose CPerron hCPerronPos hPerron using
    exists_norm_centeredVerticalIntegral_sub_halfSum_le_sourceScale
  let CResidual : Real :=
    CPerron +
      ((108 / Real.pi) * CHeight +
        (6 / Real.pi) * (1 + CLeft))
  have hCResidualPos : 0 < CResidual := by
    dsimp [CResidual]
    positivity
  refine Exists.intro CHeight
    (Exists.intro CResidual
      (And.intro hCHeightPos (And.intro hCResidualPos ?_)))
  intro N inst hN chi hchi hPrimitive x hx
    T hT hTx c0 exceptional hChoice
  let data : SelectedHeightContourData chi x T CHeight exceptional :=
    Classical.choice
      (hData hN hchi hPrimitive x hx T hT c0 exceptional hChoice)
  have hPerronData :=
    hPerron hN chi hx hT hTx data.height_lower
  have hBoundaryData :=
    hBoundary hN hchi hPrimitive hx hCHeightPos.le
      hT hTx data
  have hCombined :=
    norm_centeredFormulaResidual_le data hPerronData hBoundaryData
  refine Nonempty.intro {
    contour := data
    residual_bound := ?_
  }
  simpa [CResidual, add_mul] using hCombined

end BombieriVinogradov.SiegelWalfisz
