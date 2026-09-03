import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.NearTargetZeroSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Near-zero reciprocal sums under ordinate separation

This module combines a supplied all-zero ordinate gap with the independent
multiplicity-counted zero-window estimate. It bounds only the near reciprocal
sum; height selection and logarithmic derivatives remain separate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_nearZeroSum_le_of_separation :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {T K L : Real} {s : Complex},
              s.im = T ->
              0 < K ->
              0 < L ->
              Real.log N + Real.log (abs T + 2) <= L ->
              (forall p : SymmetricCompletedZeroIndex chi,
                1 / (K * L) <=
                  abs (T - (symmetricCompletedZeroValue p).im)) ->
                norm (tsum fun p : SymmetricCompletedZeroIndex chi =>
                  if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
                    1 / (s - symmetricCompletedZeroValue p)
                  else 0) <= C * K * L ^ 2) := by
  choose C hCPos hCount using exists_ncard_zeroHeightWindow_le
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T K L s hsIm hK hL hScaleLe hGap
  let nearTarget : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
      1 / (s - symmetricCompletedZeroValue p)
    else 0
  have hWindowData := hCount hN hchi hPrimitive T
  have hFinite := hWindowData.1
  have hCountRaw := hWindowData.2
  have hNearSummable : Summable nearTarget := by
    simpa [nearTarget] using
      summable_nearZero_reciprocal hchi hPrimitive T s
  have hKLPos : 0 < K * L := mul_pos hK hL
  have hTermBound : forall p : SymmetricCompletedZeroIndex chi,
      norm (nearTarget p) <= K * L := by
    intro p
    by_cases hpWindow :
        abs (T - (symmetricCompletedZeroValue p).im) < 1
    case pos =>
      have hDenIm :
          (s - symmetricCompletedZeroValue p).im =
            T - (symmetricCompletedZeroValue p).im := by
        rw [Complex.sub_im, hsIm]
      have hAbsImLe :
          abs (T - (symmetricCompletedZeroValue p).im) <=
            norm (s - symmetricCompletedZeroValue p) := by
        calc
          abs (T - (symmetricCompletedZeroValue p).im) =
              abs (s - symmetricCompletedZeroValue p).im := by
            rw [hDenIm]
          _ <= norm (s - symmetricCompletedZeroValue p) :=
            Complex.abs_im_le_norm _
      have hDenLower :
          1 / (K * L) <= norm (s - symmetricCompletedZeroValue p) :=
        (hGap p).trans hAbsImLe
      have hBasePos : 0 < 1 / (K * L) :=
        div_pos (by norm_num) hKLPos
      have hReciprocalBound :
          norm (1 / (s - symmetricCompletedZeroValue p)) <= K * L := by
        calc
          norm (1 / (s - symmetricCompletedZeroValue p)) =
              1 / norm (s - symmetricCompletedZeroValue p) := by
            rw [norm_div, norm_one]
          _ <= 1 / (1 / (K * L)) :=
            one_div_le_one_div_of_le hBasePos hDenLower
          _ = K * L := by
            field_simp
      calc
        norm (nearTarget p) =
            norm (1 / (s - symmetricCompletedZeroValue p)) := by
          dsimp [nearTarget]
          rw [if_pos hpWindow]
        _ <= K * L := hReciprocalBound
    case neg =>
      calc
        norm (nearTarget p) = 0 := by
          dsimp [nearTarget]
          rw [if_neg hpWindow, norm_zero]
        _ <= K * L := hKLPos.le
  have hCardBound :
      (hFinite.toFinset.card : Real) <= C * L := by
    calc
      (hFinite.toFinset.card : Real) =
          ((zeroHeightWindow (chi := chi) T).ncard : Real) := by
        rw [Set.ncard_eq_toFinset_card _ hFinite]
      _ <= C * (Real.log N + Real.log (abs T + 2)) := hCountRaw
      _ <= C * L :=
        mul_le_mul_of_nonneg_left hScaleLe hCPos.le
  change norm (tsum nearTarget) <= C * K * L ^ 2
  calc
    norm (tsum nearTarget) <=
        tsum (fun p => norm (nearTarget p)) :=
      norm_tsum_le_tsum_norm hNearSummable.norm
    _ = Finset.sum hFinite.toFinset (fun p => norm (nearTarget p)) :=
      tsum_eq_sum (fun p hpOutside => by
        have hpNotNear :
            Not (abs (T - (symmetricCompletedZeroValue p).im) < 1) := by
          intro hpNear
          apply hpOutside
          apply (hFinite.mem_toFinset).mpr
          change abs (T - (symmetricCompletedZeroValue p).im) < 1
          exact hpNear
        dsimp [nearTarget]
        rw [if_neg hpNotNear, norm_zero])
    _ <= Finset.sum hFinite.toFinset (fun _ => K * L) :=
      Finset.sum_le_sum (fun p _ => hTermBound p)
    _ = (hFinite.toFinset.card : Real) * (K * L) := by
      simp
    _ <= (C * L) * (K * L) :=
      mul_le_mul_of_nonneg_right hCardBound hKLPos.le
    _ = C * K * L ^ 2 := by
      ring

end BombieriVinogradov.SiegelWalfisz
