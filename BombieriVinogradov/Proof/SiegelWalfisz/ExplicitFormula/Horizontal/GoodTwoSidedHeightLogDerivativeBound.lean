import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.GoodTwoSidedZeroHeight
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.SelectedHeightScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.SeparatedSignedHeightLFunctionData
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# L-function data at one common two-sided good height

This module selects one contour height and proves nonvanishing and
log-squared logarithmic-derivative bounds at both horizontal signs.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_goodTwoSidedHeight_logDeriv_LFunction_le_sq :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real, 2 <= T ->
              exists Tprime : Real, And (T <= Tprime)
                (And (Tprime <= T + 1)
                  (And
                    (forall {s : Complex},
                      s.im = Tprime ->
                      -(1 : Real) / 2 <= s.re ->
                      s.re <= 2 ->
                        And (Ne (chi.LFunction s) 0)
                          (norm (logDeriv chi.LFunction s) <=
                            C * (zeroHeightLogScale N T) ^ 2))
                    (forall {s : Complex},
                      s.im = -Tprime ->
                      -(1 : Real) / 2 <= s.re ->
                      s.re <= 2 ->
                        And (Ne (chi.LFunction s) 0)
                          (norm (logDeriv chi.LFunction s) <=
                            C * (zeroHeightLogScale N T) ^ 2))))) := by
  choose CHeight hCHeightPos hHeight using
    exists_goodTwoSidedZeroHeight
  choose CData hCDataPos hData using
    exists_LFunction_data_of_separation
  let C : Real := CData * (CHeight + 1)
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T hT
  choose Tprime hTprimeLower hTprimeUpper hGap using
    hHeight hN hchi hPrimitive T hT
  have hScaleData :=
    selectedHeight_scale_data hN hT hTprimeLower hTprimeUpper
  let L : Real := zeroHeightLogScale N T
  have hLOne : 1 <= L := by
    simpa [L] using hScaleData.1
  have hAbsTprime : 2 <= abs Tprime :=
    hScaleData.2.1
  have hScaleLe :
      Real.log N + Real.log (abs Tprime + 2) <= L := by
    simpa [L] using hScaleData.2.2
  have hTprimePos : 0 < Tprime := by
    linarith
  have hTprimeNe : Ne Tprime 0 :=
    ne_of_gt hTprimePos
  have hNegTprimeNe : Ne (-Tprime) 0 :=
    neg_ne_zero.mpr hTprimeNe
  have hTopGap : forall p : SymmetricCompletedZeroIndex chi,
      1 / (CHeight * L) <=
        abs (Tprime - (symmetricCompletedZeroValue p).im) := by
    intro p
    simpa [L] using (hGap p).1
  have hBottomGap : forall p : SymmetricCompletedZeroIndex chi,
      1 / (CHeight * L) <=
        abs ((-Tprime) - (symmetricCompletedZeroValue p).im) := by
    intro p
    simpa [L] using (hGap p).2
  have hTop : forall {s : Complex},
      s.im = Tprime ->
      -(1 : Real) / 2 <= s.re ->
      s.re <= 2 ->
        And (Ne (chi.LFunction s) 0)
          (norm (logDeriv chi.LFunction s) <=
            C * (zeroHeightLogScale N T) ^ 2) := by
    intro s hsIm hsLower hsUpper
    have hTopData :=
      hData hN hchi hPrimitive hsIm hsLower hsUpper
        hAbsTprime hTprimeNe hCHeightPos hLOne hScaleLe hTopGap
    exact And.intro hTopData.1 (by
      simpa [C, L] using hTopData.2)
  have hBottom : forall {s : Complex},
      s.im = -Tprime ->
      -(1 : Real) / 2 <= s.re ->
      s.re <= 2 ->
        And (Ne (chi.LFunction s) 0)
          (norm (logDeriv chi.LFunction s) <=
            C * (zeroHeightLogScale N T) ^ 2) := by
    intro s hsIm hsLower hsUpper
    have hAbsNegTprime : 2 <= abs (-Tprime) := by
      simpa only [abs_neg] using hAbsTprime
    have hNegScaleLe :
        Real.log N + Real.log (abs (-Tprime) + 2) <= L := by
      simpa only [abs_neg] using hScaleLe
    have hBottomData :=
      hData hN hchi hPrimitive hsIm hsLower hsUpper
        hAbsNegTprime hNegTprimeNe hCHeightPos hLOne hNegScaleLe
        hBottomGap
    exact And.intro hBottomData.1 (by
      simpa [C, L] using hBottomData.2)
  exact Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper
      (And.intro hTop hBottom)))

end BombieriVinogradov.SiegelWalfisz
