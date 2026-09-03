import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.GoodZeroHeight
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.LocalLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.SeparatedNearZeroSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightScale
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log-squared logarithmic-derivative bounds at selected heights

This module combines the independent good-height selector, separated near-zero
sum estimate, and local logarithmic-derivative remainder theorem. It returns
both the all-zero separation and the uniform horizontal-strip bound; contour
integration remains in later modules.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_goodHeight_logDeriv_LFunction_le_sq :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real, 2 <= T ->
              exists Tprime : Real, And (T <= Tprime)
                (And (Tprime <= T + 1)
                  (And
                    (forall p : SymmetricCompletedZeroIndex chi,
                      1 / (C * zeroHeightLogScale N T) <=
                        abs (Tprime -
                          (symmetricCompletedZeroValue p).im))
                    (forall {s : Complex},
                      s.im = Tprime ->
                      -(1 : Real) / 2 <= s.re ->
                      s.re <= 2 ->
                      Ne (chi.LFunction s) 0 ->
                        norm (logDeriv chi.LFunction s) <=
                          C * (zeroHeightLogScale N T) ^ 2)))) := by
  choose CHeight hCHeightPos hGood using exists_goodZeroHeight
  choose CNear hCNearPos hNear using
    exists_norm_nearZeroSum_le_of_separation
  choose CLocal hCLocalPos hLocal using
    exists_norm_logDeriv_LFunction_sub_nearZeroSum_le
  let C : Real := CHeight + CLocal + CNear * CHeight
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T hT
  choose Tprime hTprimeLower hTprimeUpper hGap using
    hGood hN hchi hPrimitive T hT
  let L : Real := zeroHeightLogScale N T
  have hNOneNat : 1 < N := lt_of_lt_of_le (by norm_num) hN
  have hNOneRealRaw : ((1 : Nat) : Real) < (N : Real) :=
    (Nat.cast_lt).2 hNOneNat
  have hNOneReal : (1 : Real) < (N : Real) := by
    simpa using hNOneRealRaw
  have hLogNPos : 0 < Real.log N :=
    Real.log_pos hNOneReal
  have hTArgOne : (1 : Real) < T + 3 := by
    linarith
  have hLogTPos : 0 < Real.log (T + 3) :=
    Real.log_pos hTArgOne
  have hScaleOne : 1 <= L := by
    dsimp [L, zeroHeightLogScale]
    linarith
  have hScalePos : 0 < L := lt_of_lt_of_le (by norm_num) hScaleOne
  have hGapL : forall p : SymmetricCompletedZeroIndex chi,
      1 / (CHeight * L) <=
        abs (Tprime - (symmetricCompletedZeroValue p).im) := by
    intro p
    simpa [L] using hGap p
  have hExpandedGap : forall p : SymmetricCompletedZeroIndex chi,
      1 / (C * zeroHeightLogScale N T) <=
        abs (Tprime - (symmetricCompletedZeroValue p).im) := by
    intro p
    have hExtraNonneg : 0 <= CNear * CHeight :=
      mul_nonneg hCNearPos.le hCHeightPos.le
    have hDenLe :
        CHeight * zeroHeightLogScale N T <=
          C * zeroHeightLogScale N T := by
      apply mul_le_mul_of_nonneg_right
      dsimp [C]
      linarith
      exact hScalePos.le
    have hBasePos : 0 < CHeight * zeroHeightLogScale N T := by
      exact mul_pos hCHeightPos (by simpa [L] using hScalePos)
    exact
      (one_div_le_one_div_of_le hBasePos hDenLe).trans (hGap p)
  refine Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper
      (And.intro hExpandedGap ?_)))
  intro s hsIm hsLower hsUpper hLFunctionNe
  let nearTarget : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    if abs (Tprime - (symmetricCompletedZeroValue p).im) < 1 then
      1 / (s - symmetricCompletedZeroValue p)
    else 0
  have hTprimeNonneg : 0 <= Tprime :=
    le_trans (by linarith) hTprimeLower
  have hAbsTprime : abs Tprime = Tprime :=
    abs_of_nonneg hTprimeNonneg
  have hCurrentArgPos : 0 < abs Tprime + 2 := by
    linarith [abs_nonneg Tprime]
  have hCurrentArgLe : abs Tprime + 2 <= T + 3 := by
    rw [hAbsTprime]
    linarith
  have hCurrentLogLe :
      Real.log (abs Tprime + 2) <= Real.log (T + 3) :=
    Real.log_le_log hCurrentArgPos hCurrentArgLe
  have hCurrentScaleLe :
      Real.log N + Real.log (abs Tprime + 2) <= L := by
    dsimp [L, zeroHeightLogScale]
    linarith
  have hAbsTprimeLower : 2 <= abs Tprime := by
    rw [hAbsTprime]
    exact le_trans hT hTprimeLower
  have hNearBound :
      norm (tsum nearTarget) <= CNear * CHeight * L ^ 2 := by
    simpa [nearTarget] using
      hNear hN hchi hPrimitive hsIm hCHeightPos hScalePos
        hCurrentScaleLe hGapL
  have hLocalRaw :
      norm (logDeriv chi.LFunction s - tsum nearTarget) <=
        CLocal *
          (Real.log N + Real.log (abs Tprime + 2)) := by
    simpa [nearTarget] using
      hLocal hN hchi hPrimitive hsIm hsLower hsUpper
        hAbsTprimeLower hLFunctionNe
  have hLocalLeL :
      norm (logDeriv chi.LFunction s - tsum nearTarget) <=
        CLocal * L :=
    hLocalRaw.trans
      (mul_le_mul_of_nonneg_left hCurrentScaleLe hCLocalPos.le)
  have hScaleMulNonneg : 0 <= L * (L - 1) :=
    mul_nonneg hScalePos.le (sub_nonneg.mpr hScaleOne)
  have hScaleLeSq : L <= L ^ 2 := by
    nlinarith
  have hLocalBound :
      norm (logDeriv chi.LFunction s - tsum nearTarget) <=
        CLocal * L ^ 2 :=
    hLocalLeL.trans
      (mul_le_mul_of_nonneg_left hScaleLeSq hCLocalPos.le)
  have hDecompose :
      logDeriv chi.LFunction s =
        (logDeriv chi.LFunction s - tsum nearTarget) +
          tsum nearTarget := by
    ring
  calc
    norm (logDeriv chi.LFunction s) =
        norm ((logDeriv chi.LFunction s - tsum nearTarget) +
          tsum nearTarget) :=
      congrArg norm hDecompose
    _ <= norm (logDeriv chi.LFunction s - tsum nearTarget) +
        norm (tsum nearTarget) :=
      norm_add_le _ _
    _ <= CLocal * L ^ 2 + CNear * CHeight * L ^ 2 :=
      add_le_add hLocalBound hNearBound
    _ <= C * L ^ 2 := by
      dsimp [C]
      have hScaleSqNonneg : 0 <= L ^ 2 := sq_nonneg L
      nlinarith

end BombieriVinogradov.SiegelWalfisz
