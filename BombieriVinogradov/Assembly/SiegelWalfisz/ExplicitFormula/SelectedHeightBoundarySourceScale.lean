import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightBoundaryBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.HorizontalBoundary
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.LeftBoundary
import Mathlib.Tactic.Ring

/-!
# Selected boundary sum in the source scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_selectedHeight_boundary_sum_le_sourceScale :
    exists CLeft : Real, And (0 < CLeft)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 < x ->
              forall {T C : Real}, 0 <= C -> 2 <= T -> T <= x ->
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
        ((108 / Real.pi) * C + (6 / Real.pi) * (1 + CLeft)) *
          ((x : Real) / T *
            (Real.log ((N * x : Nat) : Real)) ^ 2)) := by
  choose CLeft hCLeftPos hBoundary using
    exists_norm_selectedHeight_boundary_sum_le
  refine Exists.intro CLeft (And.intro hCLeftPos ?_)
  intro N inst hN chi hchi hPrimitive x hx
    T C hC hT hTx exceptional data
  let A : Real :=
    (x : Real) / T * (Real.log ((N * x : Nat) : Real)) ^ 2
  have hExact :=
    hBoundary (N := N) (chi := chi) hchi hPrimitive
      (x := x) hx (T := T) (C := C) hT
      (exceptional := exceptional) data
  have hBottom :
      (1 / (2 * Real.pi)) *
          ((C * (zeroHeightLogScale N T) ^ 2) *
            (4 * (x : Real) / abs (-data.height)) *
              abs ((-(1 : Real) / 2) - optimizedPerronLine x)) <=
        (54 / Real.pi) * C * A := by
    simpa [A] using
      bottomHorizontalMajorant_le_sourceScale
        hC hN hx hT hTx data.height_lower
  have hLeft :
      (6 / Real.pi) *
          (abs (Real.log N) + CLeft * Real.log (data.height + 2)) *
            Real.log (data.height + 1) <=
        (6 / Real.pi) * (1 + CLeft) * A := by
    simpa [A] using
      leftBoundaryMajorant_le_sourceScale hCLeftPos.le
        hN hx hT hTx data.height_lower data.height_upper
  have hTop :
      (1 / (2 * Real.pi)) *
          ((C * (zeroHeightLogScale N T) ^ 2) *
            (4 * (x : Real) / abs data.height) *
              abs (optimizedPerronLine x - (-(1 : Real) / 2))) <=
        (54 / Real.pi) * C * A := by
    simpa [A] using
      topHorizontalMajorant_le_sourceScale
        hC hN hx hT hTx data.height_lower
  calc
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
              abs (optimizedPerronLine x - (-(1 : Real) / 2))) :=
      hExact
    _ <= (54 / Real.pi) * C * A +
        (6 / Real.pi) * (1 + CLeft) * A +
        (54 / Real.pi) * C * A :=
      add_le_add (add_le_add hBottom hLeft) hTop
    _ = ((108 / Real.pi) * C +
          (6 / Real.pi) * (1 + CLeft)) * A := by
      ring
    _ = ((108 / Real.pi) * C +
          (6 / Real.pi) * (1 + CLeft)) *
        ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2) := by
      rfl

end BombieriVinogradov.SiegelWalfisz
