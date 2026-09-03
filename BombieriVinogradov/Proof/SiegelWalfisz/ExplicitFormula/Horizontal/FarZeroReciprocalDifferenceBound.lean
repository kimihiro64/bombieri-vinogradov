import BombieriVinogradov.Helpers.ComplexAnalysis.ReciprocalHorizontalDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWeightSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWeightedSumBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Far-zero reciprocal-difference sum

This module sums the pointwise reciprocal-difference estimate over zeros
whose ordinate is at least one unit from the horizontal height. Near zeros
and completed logarithmic-derivative identities remain separate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_tsum_norm_horizontal_reciprocal_difference_far_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {T : Real} {s : Complex},
              s.im = T ->
              -(1 : Real) / 2 <= s.re ->
              s.re <= 2 ->
                (tsum fun p : SymmetricCompletedZeroIndex chi =>
                  if 1 <= abs (T - (symmetricCompletedZeroValue p).im) then
                    norm (1 / (s - symmetricCompletedZeroValue p) -
                      1 / (((2 : Real) : Complex) +
                        (T : Complex) * Complex.I -
                          symmetricCompletedZeroValue p))
                  else 0) <=
                    C * (Real.log N + Real.log (abs T + 2))) := by
  choose C hCPos hWeightBound using exists_tsum_zero_vertical_weight_le
  refine Exists.intro (6 * C) (And.intro (by nlinarith) ?_)
  intro N inst hN chi hchi hPrimitive T s hsIm hsLower hsUpper
  let weight : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)
  let farTerm : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    if 1 <= abs (T - (symmetricCompletedZeroValue p).im) then
      norm (1 / (s - symmetricCompletedZeroValue p) -
        1 / (((2 : Real) : Complex) + (T : Complex) * Complex.I -
          symmetricCompletedZeroValue p))
    else 0
  have hWeightSummable : Summable weight := by
    simpa [weight] using
      summable_zero_vertical_weight hchi hPrimitive T
  have hFarTermNonneg : forall p : SymmetricCompletedZeroIndex chi,
      0 <= farTerm p := by
    intro p
    dsimp [farTerm]
    by_cases hp : 1 <= abs (T - (symmetricCompletedZeroValue p).im)
    case pos =>
      rw [if_pos hp]
      exact norm_nonneg _
    case neg =>
      rw [if_neg hp]
  have hPointwise : forall p : SymmetricCompletedZeroIndex chi,
      farTerm p <= 6 * weight p := by
    intro p
    dsimp [farTerm, weight]
    by_cases hp : 1 <= abs (T - (symmetricCompletedZeroValue p).im)
    case pos =>
      rw [if_pos hp]
      exact
        BombieriVinogradov.ComplexAnalysis.norm_horizontal_reciprocal_difference_le
          hsIm hsLower hsUpper hp
    case neg =>
      rw [if_neg hp]
      have hDenNonneg :
          0 <= 1 + (T - (symmetricCompletedZeroValue p).im) ^ 2 := by
        nlinarith [sq_nonneg (T - (symmetricCompletedZeroValue p).im)]
      exact mul_nonneg (by norm_num)
        (div_nonneg (by norm_num) hDenNonneg)
  have hScaledWeightSummable : Summable (fun p => 6 * weight p) :=
    hWeightSummable.mul_left 6
  have hFarTermSummable : Summable farTerm :=
    Summable.of_nonneg_of_le hFarTermNonneg hPointwise
      hScaledWeightSummable
  have hWeightAtT :
      tsum weight <=
        C * (Real.log N + Real.log (abs T + 2)) := by
    simpa [weight] using hWeightBound hN hchi hPrimitive T
  change tsum farTerm <=
    6 * C * (Real.log N + Real.log (abs T + 2))
  calc
    tsum farTerm <= tsum (fun p => 6 * weight p) :=
      hFarTermSummable.tsum_le_tsum hPointwise hScaledWeightSummable
    _ = 6 * tsum weight := hWeightSummable.tsum_mul_left 6
    _ <= 6 * (C * (Real.log N + Real.log (abs T + 2))) :=
      mul_le_mul_of_nonneg_left hWeightAtT (by norm_num)
    _ = 6 * C * (Real.log N + Real.log (abs T + 2)) := by
      ring

end BombieriVinogradov.SiegelWalfisz

