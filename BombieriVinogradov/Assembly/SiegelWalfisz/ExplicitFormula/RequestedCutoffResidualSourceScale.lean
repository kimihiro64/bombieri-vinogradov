import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightResidualData
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightResidualSourceScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.ZeroCutoff
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centered residual at the requested zero cutoff
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_centeredExplicitFormula_requestedCutoff_le_sourceScale :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 < x ->
              forall {T : Real}, 2 <= T -> T <= x ->
                forall {c0 : Real} {exceptional : Option Complex},
                  IsExceptionalZeroChoice c0 chi exceptional ->
                    norm
                        (characterChebyshevHalfSum x chi +
                          (lFunctionOriginMultiplicity chi : Complex) *
                            Complex.log (x : Complex) +
                          centeredTruncatedCriticalZeroSum
                            chi x T exceptional -
                          centeredExceptionalResidueSum
                            chi x exceptional) <=
                      C * ((x : Real) / T *
                        (Real.log ((N * x : Nat) : Real)) ^ 2)) := by
  choose CHeight CResidual hCHeightPos hCResidualPos hData using
    exists_selectedHeightResidualData_sourceScale
  choose CCutoff hCCutoffPos hCutoff using
    exists_norm_centeredTruncatedCriticalZeroSum_cutoffTransfer_le_sourceScale
  refine Exists.intro (CResidual + CCutoff)
    (And.intro (add_pos hCResidualPos hCCutoffPos) ?_)
  intro N inst hN chi hchi hPrimitive x hx
    T hT hTx c0 exceptional hChoice
  let data : SelectedHeightResidualData chi x T
      CHeight CResidual exceptional :=
    Classical.choice
      (hData hN hchi hPrimitive hx hT hTx hChoice)
  have hTransfer :=
    hCutoff hN hchi hPrimitive hx hT hTx
      data.contour.height_lower data.contour.height_upper exceptional
  have hIdentity :
      characterChebyshevHalfSum x chi +
            (lFunctionOriginMultiplicity chi : Complex) *
              Complex.log (x : Complex) +
            centeredTruncatedCriticalZeroSum chi x T exceptional -
            centeredExceptionalResidueSum chi x exceptional =
        (characterChebyshevHalfSum x chi +
            (lFunctionOriginMultiplicity chi : Complex) *
              Complex.log (x : Complex) +
            centeredTruncatedCriticalZeroSum
              chi x data.contour.height exceptional -
            centeredExceptionalResidueSum chi x exceptional) -
          (centeredTruncatedCriticalZeroSum
              chi x data.contour.height exceptional -
            centeredTruncatedCriticalZeroSum chi x T exceptional) := by
    ring
  rw [hIdentity]
  calc
    norm
        ((characterChebyshevHalfSum x chi +
            (lFunctionOriginMultiplicity chi : Complex) *
              Complex.log (x : Complex) +
            centeredTruncatedCriticalZeroSum
              chi x data.contour.height exceptional -
            centeredExceptionalResidueSum chi x exceptional) -
          (centeredTruncatedCriticalZeroSum
              chi x data.contour.height exceptional -
            centeredTruncatedCriticalZeroSum chi x T exceptional)) <=
      norm
          (characterChebyshevHalfSum x chi +
            (lFunctionOriginMultiplicity chi : Complex) *
              Complex.log (x : Complex) +
            centeredTruncatedCriticalZeroSum
              chi x data.contour.height exceptional -
            centeredExceptionalResidueSum chi x exceptional) +
        norm
          (centeredTruncatedCriticalZeroSum
              chi x data.contour.height exceptional -
            centeredTruncatedCriticalZeroSum chi x T exceptional) :=
      norm_sub_le _ _
    _ <= CResidual * ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2) +
        CCutoff * ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2) :=
      add_le_add data.residual_bound hTransfer
    _ = (CResidual + CCutoff) * ((x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2) := by
      ring

end BombieriVinogradov.SiegelWalfisz
