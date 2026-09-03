import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.LeftBoundaryIntegralBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightContourData
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Selected-height total boundary bound

This module combines the selected top and bottom estimates with the
independent left-boundary theorem, without changing the selected height.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_selectedHeight_boundary_sum_le :
    exists CLeft : Real, And (0 < CLeft)
      (forall {N : Nat} [NeZero N]
        {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 < x ->
              forall {T C : Real}, 2 <= T ->
                forall {exceptional : Option Complex},
                  forall data :
                    SelectedHeightContourData chi x T C exceptional,
      norm
          (centeredExplicitFormulaBottomBoundaryIntegral chi x
              ((1 : Real) / 2) (optimizedPerronLine x) data.height +
            centeredExplicitFormulaLeftBoundaryIntegral chi x
              ((1 : Real) / 2) data.height +
            centeredExplicitFormulaTopBoundaryIntegral chi x
              ((1 : Real) / 2) (optimizedPerronLine x) data.height) <=
        (1 / (2 * Real.pi)) *
            ((C * (zeroHeightLogScale N T) ^ 2) *
              (4 * (x : Real) / abs (-data.height)) *
                abs ((-(1 : Real) / 2) - optimizedPerronLine x)) +
          (6 / Real.pi) *
            (abs (Real.log N) + CLeft * Real.log (data.height + 2)) *
              Real.log (data.height + 1) +
          (1 / (2 * Real.pi)) *
            ((C * (zeroHeightLogScale N T) ^ 2) *
              (4 * (x : Real) / abs data.height) *
                abs (optimizedPerronLine x - (-(1 : Real) / 2)))) := by
  choose CLeft hCLeftPos hLeft using
    exists_norm_centered_left_boundary_integral_le
  refine Exists.intro CLeft (And.intro hCLeftPos ?_)
  intro N inst chi hchi hPrimitive x hx T C hT exceptional data
  have hxOne : 1 <= x :=
    le_trans (by norm_num) (Nat.le_of_lt hx)
  have hHeightNonneg : 0 <= data.height := by
    linarith [data.height_lower]
  have hLeftBound :
      norm (centeredExplicitFormulaLeftBoundaryIntegral chi x
        ((1 : Real) / 2) data.height) <=
          (6 / Real.pi) *
            (abs (Real.log N) + CLeft * Real.log (data.height + 2)) *
              Real.log (data.height + 1) :=
    hLeft hchi hPrimitive hxOne hHeightNonneg
  calc
    norm
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) data.height +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) data.height) <=
      norm
          (centeredExplicitFormulaBottomBoundaryIntegral chi x
              ((1 : Real) / 2) (optimizedPerronLine x) data.height +
            centeredExplicitFormulaLeftBoundaryIntegral chi x
              ((1 : Real) / 2) data.height) +
        norm (centeredExplicitFormulaTopBoundaryIntegral chi x
          ((1 : Real) / 2) (optimizedPerronLine x) data.height) :=
      norm_add_le _ _
    _ <=
      (norm (centeredExplicitFormulaBottomBoundaryIntegral chi x
          ((1 : Real) / 2) (optimizedPerronLine x) data.height) +
        norm (centeredExplicitFormulaLeftBoundaryIntegral chi x
          ((1 : Real) / 2) data.height)) +
        norm (centeredExplicitFormulaTopBoundaryIntegral chi x
          ((1 : Real) / 2) (optimizedPerronLine x) data.height) :=
      add_le_add (norm_add_le _ _) le_rfl
    _ <= _ :=
      add_le_add (add_le_add data.bottom_bound hLeftBound) data.top_bound

end BombieriVinogradov.SiegelWalfisz
