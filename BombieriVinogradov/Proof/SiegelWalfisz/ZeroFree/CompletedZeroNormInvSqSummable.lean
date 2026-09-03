import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWeightSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Squared inverse-norm summability for completed zeros

This module gives an ASCII interface for the genus-one convergence input.
Zeros of ordinate below one form a finite set; outside it, squared inverse
norms are dominated by the quadratic vertical weight at height zero.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_completedZero_norm_inv_sq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Summable (fun p : SymmetricCompletedZeroIndex chi =>
      (1 / norm (symmetricCompletedZeroValue p)) ^ 2) := by
  let term : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    (1 / norm (symmetricCompletedZeroValue p)) ^ 2
  let nearTerm : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    if abs (0 - (symmetricCompletedZeroValue p).im) < 1 then
      term p
    else 0
  let farTerm : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    if 1 <= abs (0 - (symmetricCompletedZeroValue p).im) then
      term p
    else 0
  let weight : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    1 / (1 + (0 - (symmetricCompletedZeroValue p).im) ^ 2)
  have hNearSupport : Function.HasFiniteSupport nearTerm := by
    refine (finite_zeroHeightWindow hchi hPrimitive 0).subset ?_
    intro p hp
    change abs (0 - (symmetricCompletedZeroValue p).im) < 1
    by_contra hNot
    apply hp
    dsimp [nearTerm]
    rw [if_neg hNot]
  have hNearSummable : Summable nearTerm :=
    summable_of_hasFiniteSupport hNearSupport
  have hWeightSummable : Summable weight := by
    simpa [weight] using
      summable_zero_vertical_weight hchi hPrimitive 0
  have hFarNonneg : forall p : SymmetricCompletedZeroIndex chi,
      0 <= farTerm p := by
    intro p
    dsimp [farTerm]
    by_cases hp : 1 <= abs (0 - (symmetricCompletedZeroValue p).im)
    case pos =>
      rw [if_pos hp]
      exact sq_nonneg (1 / norm (symmetricCompletedZeroValue p))
    case neg =>
      rw [if_neg hp]
  have hFarPointwise : forall p : SymmetricCompletedZeroIndex chi,
      farTerm p <= 2 * weight p := by
    intro p
    have hWeightNonneg : 0 <= weight p := by
      dsimp [weight]
      have hSquareNonneg :
          0 <= (0 - (symmetricCompletedZeroValue p).im) ^ 2 :=
        sq_nonneg (0 - (symmetricCompletedZeroValue p).im)
      have hDenNonneg :
          0 <= 1 + (0 - (symmetricCompletedZeroValue p).im) ^ 2 := by
        linarith
      exact div_nonneg (by norm_num) hDenNonneg
    dsimp [farTerm]
    by_cases hp : 1 <= abs (0 - (symmetricCompletedZeroValue p).im)
    case neg =>
      rw [if_neg hp]
      exact mul_nonneg (by norm_num) hWeightNonneg
    case pos =>
      rw [if_pos hp]
      let rho : Complex := symmetricCompletedZeroValue p
      let d : Real := abs (0 - rho.im)
      have hDOne : 1 <= d := by
        simpa [d, rho] using hp
      have hDPos : 0 < d := lt_of_lt_of_le (by norm_num) hDOne
      have hStrip : Set.Ioo 0 1 rho.re := by
        simpa [rho] using
          symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p
      have hRhoNe : Ne rho 0 := by
        intro hRhoZero
        have hRhoRePos := hStrip.1
        rw [hRhoZero] at hRhoRePos
        norm_num at hRhoRePos
      have hNormPos : 0 < norm rho := norm_pos_iff.mpr hRhoNe
      have hDNorm : d <= norm rho := by
        dsimp [d]
        calc
          abs (0 - rho.im) = abs rho.im := by
            rw [zero_sub, abs_neg]
          _ <= norm rho := Complex.abs_im_le_norm rho
      have hInv : 1 / norm rho <= 1 / d :=
        one_div_le_one_div_of_le hDPos hDNorm
      have hTermLeInvSq : term p <= (1 / d) ^ 2 := by
        dsimp [term, rho]
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self
          (div_nonneg (by norm_num) hNormPos.le) hInv
      have hWeightDen : 1 + d ^ 2 <= 2 * d ^ 2 := by
        nlinarith
      have hReciprocal :
          1 / (2 * d ^ 2) <= 1 / (1 + d ^ 2) :=
        one_div_le_one_div_of_le
          (by nlinarith [sq_nonneg d]) hWeightDen
      have hInvSqIdentity :
          (1 / d) ^ 2 = 2 * (1 / (2 * d ^ 2)) := by
        field_simp [ne_of_gt hDPos]
      have hInvSqWeight :
          (1 / d) ^ 2 <= 2 * (1 / (1 + d ^ 2)) := by
        rw [hInvSqIdentity]
        exact mul_le_mul_of_nonneg_left hReciprocal (by norm_num)
      have hDsq : d ^ 2 = (0 - rho.im) ^ 2 := by
        dsimp [d]
        exact sq_abs (0 - rho.im)
      calc
        term p <= (1 / d) ^ 2 := hTermLeInvSq
        _ <= 2 * (1 / (1 + d ^ 2)) := hInvSqWeight
        _ = 2 * weight p := by
          rw [hDsq]
  have hScaledWeightSummable : Summable (fun p => 2 * weight p) :=
    hWeightSummable.mul_left 2
  have hFarSummable : Summable farTerm :=
    Summable.of_nonneg_of_le hFarNonneg hFarPointwise
      hScaledWeightSummable
  have hTermSplit : forall p : SymmetricCompletedZeroIndex chi,
      term p = nearTerm p + farTerm p := by
    intro p
    dsimp [nearTerm, farTerm]
    by_cases hp : abs (0 - (symmetricCompletedZeroValue p).im) < 1
    case pos =>
      have hNotFar : Not (1 <=
          abs (0 - (symmetricCompletedZeroValue p).im)) :=
        not_le_of_gt hp
      rw [if_pos hp, if_neg hNotFar, add_zero]
    case neg =>
      have hIsFar : 1 <=
          abs (0 - (symmetricCompletedZeroValue p).im) :=
        le_of_not_gt hp
      rw [if_neg hp, if_pos hIsFar, zero_add]
  have hCombined : Summable (fun p => nearTerm p + farTerm p) :=
    hNearSummable.add hFarSummable
  have hFunction : term = fun p => nearTerm p + farTerm p := by
    funext p
    exact hTermSplit p
  change Summable term
  rw [hFunction]
  exact hCombined

end BombieriVinogradov.SiegelWalfisz

