import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.FarZeroReciprocalDifferenceBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.NearReferenceZeroBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.NearTargetZeroSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroReciprocalDifferenceSummable
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Remainder after isolating near completed zeros

This module splits the two-point reciprocal-difference series at the open
unit zero-height window and bounds the remaining near-reference and far-zero
contributions. L-function and gamma-factor terms remain outside this module.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_tsum_zeroDifference_sub_near_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {T : Real} {s : Complex},
              s.im = T ->
              -(1 : Real) / 2 <= s.re ->
              s.re <= 2 ->
              (forall p : SymmetricCompletedZeroIndex chi,
                Ne s (symmetricCompletedZeroValue p)) ->
                norm (
                  (tsum fun p : SymmetricCompletedZeroIndex chi =>
                    1 / (s - symmetricCompletedZeroValue p) -
                      1 / (((2 : Real) : Complex) +
                        (T : Complex) * Complex.I -
                          symmetricCompletedZeroValue p)) -
                  (tsum fun p : SymmetricCompletedZeroIndex chi =>
                    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
                      1 / (s - symmetricCompletedZeroValue p)
                    else 0)) <=
                      C * (Real.log N + Real.log (abs T + 2))) := by
  choose CNear hCNearPos hNear using
    exists_tsum_norm_reference_reciprocal_near_le
  choose CFar hCFarPos hFar using
    exists_tsum_norm_horizontal_reciprocal_difference_far_le
  refine Exists.intro (CNear + CFar)
    (And.intro (add_pos hCNearPos hCFarPos) ?_)
  intro N inst hN chi hchi hPrimitive T s hsIm hsLower hsUpper hsAway
  let w : Complex :=
    ((2 : Real) : Complex) + (T : Complex) * Complex.I
  let zeroDiff : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    1 / (s - symmetricCompletedZeroValue p) -
      1 / (w - symmetricCompletedZeroValue p)
  let nearTarget : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
      1 / (s - symmetricCompletedZeroValue p)
    else 0
  let remTerm : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    zeroDiff p - nearTarget p
  let nearNorm : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
      norm (1 / (w - symmetricCompletedZeroValue p))
    else 0
  let farNorm : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    if 1 <= abs (T - (symmetricCompletedZeroValue p).im) then
      norm (1 / (s - symmetricCompletedZeroValue p) -
        1 / (w - symmetricCompletedZeroValue p))
    else 0
  have hwRe : w.re = 2 := by
    simp [w, Complex.mul_re]
  have hwAway : forall p : SymmetricCompletedZeroIndex chi,
      Ne w (symmetricCompletedZeroValue p) := by
    intro p hEqual
    have hUpper : (symmetricCompletedZeroValue p).re < 1 :=
      (symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p).2
    rw [Eq.symm hEqual, hwRe] at hUpper
    norm_num at hUpper
  have hZeroDiffSummable : Summable zeroDiff := by
    simpa [zeroDiff] using
      summable_completedZero_reciprocalDifference
        hchi hPrimitive hsAway hwAway
  have hNearTargetSummable : Summable nearTarget := by
    simpa [nearTarget] using
      summable_nearZero_reciprocal hchi hPrimitive T s
  have hRemSummable : Summable remTerm := by
    simpa [remTerm] using hZeroDiffSummable.sub hNearTargetSummable
  have hNearNormNonneg : forall p : SymmetricCompletedZeroIndex chi,
      0 <= nearNorm p := by
    intro p
    by_cases hp : abs (T - (symmetricCompletedZeroValue p).im) < 1
    case pos =>
      dsimp [nearNorm]
      rw [if_pos hp]
      exact norm_nonneg _
    case neg =>
      dsimp [nearNorm]
      rw [if_neg hp]
  have hFarNormNonneg : forall p : SymmetricCompletedZeroIndex chi,
      0 <= farNorm p := by
    intro p
    by_cases hp : 1 <= abs (T - (symmetricCompletedZeroValue p).im)
    case pos =>
      dsimp [farNorm]
      rw [if_pos hp]
      exact norm_nonneg _
    case neg =>
      dsimp [farNorm]
      rw [if_neg hp]
  have hNormSplit : forall p : SymmetricCompletedZeroIndex chi,
      norm (remTerm p) = nearNorm p + farNorm p := by
    intro p
    by_cases hpNear : abs (T - (symmetricCompletedZeroValue p).im) < 1
    case pos =>
      have hpFar : Not (1 <= abs (T -
          (symmetricCompletedZeroValue p).im)) :=
        not_le_of_gt hpNear
      have hAlgebra :
          (1 / (s - symmetricCompletedZeroValue p) -
              1 / (w - symmetricCompletedZeroValue p)) -
            1 / (s - symmetricCompletedZeroValue p) =
              -(1 / (w - symmetricCompletedZeroValue p)) := by
        ring
      dsimp [remTerm, zeroDiff, nearTarget, nearNorm, farNorm]
      rw [if_pos hpNear, if_neg hpFar, hAlgebra, norm_neg, add_zero]
      rw [if_pos hpNear]
    case neg =>
      have hpFar : 1 <= abs (T -
          (symmetricCompletedZeroValue p).im) :=
        le_of_not_gt hpNear
      dsimp [remTerm, zeroDiff, nearTarget, nearNorm, farNorm]
      rw [if_neg hpNear, if_pos hpFar, sub_zero]
      rw [if_neg hpNear, zero_add]
  have hRemNormSummable : Summable (fun p => norm (remTerm p)) :=
    hRemSummable.norm
  have hNearNormLe : forall p : SymmetricCompletedZeroIndex chi,
      nearNorm p <= norm (remTerm p) := by
    intro p
    calc
      nearNorm p <= nearNorm p + farNorm p :=
        le_add_of_nonneg_right (hFarNormNonneg p)
      _ = norm (remTerm p) := Eq.symm (hNormSplit p)
  have hFarNormLe : forall p : SymmetricCompletedZeroIndex chi,
      farNorm p <= norm (remTerm p) := by
    intro p
    calc
      farNorm p <= nearNorm p + farNorm p :=
        le_add_of_nonneg_left (hNearNormNonneg p)
      _ = norm (remTerm p) := Eq.symm (hNormSplit p)
  have hNearNormSummable : Summable nearNorm :=
    Summable.of_nonneg_of_le hNearNormNonneg hNearNormLe hRemNormSummable
  have hFarNormSummable : Summable farNorm :=
    Summable.of_nonneg_of_le hFarNormNonneg hFarNormLe hRemNormSummable
  have hNearBound :
      tsum nearNorm <=
        CNear * (Real.log N + Real.log (abs T + 2)) := by
    simpa [nearNorm, w] using hNear hN hchi hPrimitive T
  have hFarBound :
      tsum farNorm <=
        CFar * (Real.log N + Real.log (abs T + 2)) := by
    simpa [farNorm, w] using
      hFar hN hchi hPrimitive hsIm hsLower hsUpper
  have hTsumDifference :
      tsum remTerm = tsum zeroDiff - tsum nearTarget :=
    hZeroDiffSummable.tsum_sub hNearTargetSummable
  change norm (tsum zeroDiff - tsum nearTarget) <=
    (CNear + CFar) * (Real.log N + Real.log (abs T + 2))
  rw [Eq.symm hTsumDifference]
  calc
    norm (tsum remTerm) <=
        tsum (fun p => norm (remTerm p)) :=
      norm_tsum_le_tsum_norm hRemNormSummable
    _ = tsum (fun p => nearNorm p + farNorm p) :=
      tsum_congr hNormSplit
    _ = tsum nearNorm + tsum farNorm :=
      hNearNormSummable.tsum_add hFarNormSummable
    _ <= CNear * (Real.log N + Real.log (abs T + 2)) +
        CFar * (Real.log N + Real.log (abs T + 2)) :=
      add_le_add hNearBound hFarBound
    _ = (CNear + CFar) *
        (Real.log N + Real.log (abs T + 2)) := by
      ring

end BombieriVinogradov.SiegelWalfisz
