import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.LocalLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.SeparatedNearZeroSumBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A logarithmic-derivative bound from signed-height separation

This module bounds the L-function logarithmic derivative at an arbitrary
signed height from a supplied completed-zero ordinate gap. Height selection
and simultaneous use at both horizontal signs belong to later modules.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_LFunction_le_sq_of_separation :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {T K L : Real} {s : Complex},
              s.im = T ->
              -(1 : Real) / 2 <= s.re ->
              s.re <= 2 ->
              2 <= abs T ->
              Ne (chi.LFunction s) 0 ->
              0 < K ->
              1 <= L ->
              Real.log N + Real.log (abs T + 2) <= L ->
              (forall p : SymmetricCompletedZeroIndex chi,
                1 / (K * L) <=
                  abs (T - (symmetricCompletedZeroValue p).im)) ->
                norm (logDeriv chi.LFunction s) <=
                  C * (K + 1) * L ^ 2) := by
  choose CNear hCNearPos hNear using
    exists_norm_nearZeroSum_le_of_separation
  choose CLocal hCLocalPos hLocal using
    exists_norm_logDeriv_LFunction_sub_nearZeroSum_le
  let C : Real := CLocal + CNear
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T K L s hsIm hsLower hsUpper
    hAbsT hLFunctionNe hK hLOne hScaleLe hGap
  let nearTarget : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
      1 / (s - symmetricCompletedZeroValue p)
    else 0
  have hLPos : 0 < L := by
    linarith
  have hNearBound :
      norm (tsum nearTarget) <= CNear * K * L ^ 2 := by
    simpa [nearTarget] using
      hNear hN hchi hPrimitive hsIm hK hLPos hScaleLe hGap
  have hLocalRaw :
      norm (logDeriv chi.LFunction s - tsum nearTarget) <=
        CLocal *
          (Real.log N + Real.log (abs T + 2)) := by
    simpa [nearTarget] using
      hLocal hN hchi hPrimitive hsIm hsLower hsUpper
        hAbsT hLFunctionNe
  have hLocalLeL :
      norm (logDeriv chi.LFunction s - tsum nearTarget) <=
        CLocal * L :=
    hLocalRaw.trans
      (mul_le_mul_of_nonneg_left hScaleLe hCLocalPos.le)
  have hScaleLeSq : L <= L ^ 2 := by
    nlinarith [mul_nonneg hLPos.le (sub_nonneg.mpr hLOne)]
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
    _ <= CLocal * L ^ 2 + CNear * K * L ^ 2 :=
      add_le_add hLocalBound hNearBound
    _ = (CLocal + CNear * K) * L ^ 2 := by
      ring
    _ <= C * (K + 1) * L ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
      dsimp [C]
      nlinarith

end BombieriVinogradov.SiegelWalfisz
