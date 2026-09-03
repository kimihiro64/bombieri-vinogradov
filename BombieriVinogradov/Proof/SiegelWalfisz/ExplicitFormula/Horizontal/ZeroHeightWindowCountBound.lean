import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWeightSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWeightedSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindow
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Cardinality bounds for unit vertical zero windows

This module derives finiteness and an absolute logarithmic cardinality bound
for the multiplicity-indexed completed zeros in a unit vertical window.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- Every zero in the open unit vertical window contributes at least one half
to the standard quadratic vertical-gap weight. -/
theorem one_half_le_zero_vertical_weight_of_lt
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {p : SymmetricCompletedZeroIndex chi}
    (hp : abs (T - (symmetricCompletedZeroValue p).im) < 1) :
    (1 : Real) / 2 <=
      1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2) := by
  have hSq : (T - (symmetricCompletedZeroValue p).im) ^ 2 < 1 := by
    have hSqAbs :
        (T - (symmetricCompletedZeroValue p).im) ^ 2 < (1 : Real) ^ 2 :=
      (sq_lt_sq).2 (by simpa using hp)
    simpa using hSqAbs
  have hDenPos :
      0 < 1 + (T - (symmetricCompletedZeroValue p).im) ^ 2 := by
    nlinarith [sq_nonneg (T - (symmetricCompletedZeroValue p).im)]
  have hDenLe :
      1 + (T - (symmetricCompletedZeroValue p).im) ^ 2 <= 2 := by
    linarith
  exact one_div_le_one_div_of_le hDenPos hDenLe

/-- The multiplicity-indexed completed zeros in a unit vertical window form
a finite set. -/
theorem finite_zeroHeightWindow
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) :
    Set.Finite (zeroHeightWindow (chi := chi) T) := by
  let weight : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)
  have hSummable : Summable weight := by
    simpa [weight] using
      summable_zero_vertical_weight hchi hPrimitive T
  have hEventually :
      Filter.Eventually (fun p => weight p < (1 : Real) / 2)
        Filter.cofinite :=
    hSummable.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  have hLargeFinite :
      Set.Finite {p | Not (weight p < (1 : Real) / 2)} :=
    Filter.eventually_cofinite.mp hEventually
  refine hLargeFinite.subset ?_
  intro p hp
  change abs (T - (symmetricCompletedZeroValue p).im) < 1 at hp
  change Not (weight p < (1 : Real) / 2)
  exact not_lt_of_ge
    (by
      simpa [weight] using
        one_half_le_zero_vertical_weight_of_lt hp)

/-- One absolute positive constant bounds the multiplicity-counted number of
completed zeros in every open unit vertical window by the modulus-height
logarithm. -/
theorem exists_ncard_zeroHeightWindow_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real,
              And (Set.Finite (zeroHeightWindow (chi := chi) T))
                (((zeroHeightWindow (chi := chi) T).ncard : Real) <=
                  C * (Real.log N + Real.log (abs T + 2)))) := by
  choose C hCPos hBound using exists_tsum_zero_vertical_weight_le
  refine Exists.intro (2 * C) (And.intro (by nlinarith) ?_)
  intro N inst hN chi hchi hPrimitive T
  have hFinite : Set.Finite (zeroHeightWindow (chi := chi) T) :=
    finite_zeroHeightWindow hchi hPrimitive T
  refine And.intro hFinite ?_
  let weight : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    1 / (1 + (T - (symmetricCompletedZeroValue p).im) ^ 2)
  have hSummable : Summable weight := by
    simpa [weight] using
      summable_zero_vertical_weight hchi hPrimitive T
  have hWeightNonneg : forall p : SymmetricCompletedZeroIndex chi,
      0 <= weight p := by
    intro p
    exact div_nonneg (by norm_num)
      (by nlinarith [sq_nonneg (T - (symmetricCompletedZeroValue p).im)])
  have hCardHalf :
      ((zeroHeightWindow (chi := chi) T).ncard : Real) / 2 <=
        Finset.sum hFinite.toFinset weight := by
    rw [Set.ncard_eq_toFinset_card _ hFinite]
    calc
      (hFinite.toFinset.card : Real) / 2 =
          Finset.sum hFinite.toFinset (fun _ => (1 : Real) / 2) := by
        simp [div_eq_mul_inv]
      _ <= Finset.sum hFinite.toFinset weight :=
        Finset.sum_le_sum (fun p hp => by
          have hpWindow := (hFinite.mem_toFinset).mp hp
          change abs (T - (symmetricCompletedZeroValue p).im) < 1
            at hpWindow
          simpa [weight] using
            one_half_le_zero_vertical_weight_of_lt hpWindow)
  have hFiniteSumLeTsum :
      Finset.sum hFinite.toFinset weight <= tsum weight :=
    Summable.sum_le_tsum hFinite.toFinset
      (fun p _ => hWeightNonneg p) hSummable
  have hCountLeTsum :
      ((zeroHeightWindow (chi := chi) T).ncard : Real) / 2 <=
        tsum weight :=
    hCardHalf.trans hFiniteSumLeTsum
  have hTsumBound :
      tsum weight <= C * (Real.log N + Real.log (abs T + 2)) := by
    simpa [weight] using hBound hN hchi hPrimitive T
  nlinarith [hCountLeTsum.trans hTsumBound]

end BombieriVinogradov.SiegelWalfisz
