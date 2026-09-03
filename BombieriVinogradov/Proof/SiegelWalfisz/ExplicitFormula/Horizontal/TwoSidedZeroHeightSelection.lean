import BombieriVinogradov.Helpers.RealAnalysis.FiniteSetIntervalAvoidance
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selecting one height away from zeros at both horizontal signs

This module applies finite-set interval avoidance to positive zero ordinates
and negated negative zero ordinates simultaneously. Logarithmic normalization
belongs to a later module.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem exists_twoSidedZeroHeight_separated_by_ncard
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) :
    exists Tprime : Real, And (T <= Tprime)
      (And (Tprime <= T + 1)
        (forall p : SymmetricCompletedZeroIndex chi,
          And
            (1 / (2 *
              ((((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard +
                (zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard : Nat) :
                  Real) + 2)) <=
                abs (Tprime - (symmetricCompletedZeroValue p).im))
            (1 / (2 *
              ((((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard +
                (zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard : Nat) :
                  Real) + 2)) <=
                abs ((-Tprime) - (symmetricCompletedZeroValue p).im)))) := by
  classical
  let center : Real := T + 1 / 2
  let posWindow : Set (SymmetricCompletedZeroIndex chi) :=
    zeroHeightWindow (chi := chi) center
  let negWindow : Set (SymmetricCompletedZeroIndex chi) :=
    zeroHeightWindow (chi := chi) (-center)
  have hPosFinite : Set.Finite posWindow := by
    simpa [posWindow, center] using
      finite_zeroHeightWindow hchi hPrimitive (T + 1 / 2)
  have hNegFinite : Set.Finite negWindow := by
    simpa [negWindow, center] using
      finite_zeroHeightWindow hchi hPrimitive (-(T + 1 / 2))
  let posOrdinates : Finset Real :=
    hPosFinite.toFinset.image
      (fun p => (symmetricCompletedZeroValue p).im)
  let negOrdinates : Finset Real :=
    hNegFinite.toFinset.image
      (fun p => -(symmetricCompletedZeroValue p).im)
  let forbidden : Finset Real := Union.union posOrdinates negOrdinates
  choose Tprime hTprimeLower hTprimeUpper hAvoid using
    BombieriVinogradov.RealAnalysis.exists_unitInterval_away_from_finset
      forbidden T
  refine Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper ?_))
  intro p
  change And
    (1 / (2 *
      ((((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2))) <=
        abs (Tprime - (symmetricCompletedZeroValue p).im))
    (1 / (2 *
      ((((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2))) <=
        abs ((-Tprime) - (symmetricCompletedZeroValue p).im))
  have hForbiddenCardLe :
      forbidden.card <= posWindow.ncard + negWindow.ncard := by
    calc
      forbidden.card <= posOrdinates.card + negOrdinates.card := by
        dsimp [forbidden]
        exact Finset.card_union_le _ _
      _ <= hPosFinite.toFinset.card + hNegFinite.toFinset.card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = posWindow.ncard + negWindow.ncard := by
        rw [Set.ncard_eq_toFinset_card posWindow hPosFinite,
          Set.ncard_eq_toFinset_card negWindow hNegFinite]
  have hForbiddenCardCast :
      (forbidden.card : Real) <=
        ((posWindow.ncard + negWindow.ncard : Nat) : Real) :=
    (Nat.cast_le).2 hForbiddenCardLe
  have hSmallDenPos : 0 < 2 * ((forbidden.card : Real) + 2) := by
    positivity
  have hDenLe :
      2 * ((forbidden.card : Real) + 2) <=
        2 * (((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2) := by
    linarith
  have hRadiusMono :
      1 / (2 *
          (((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2)) <=
        1 / (2 * ((forbidden.card : Real) + 2)) :=
    one_div_le_one_div_of_le hSmallDenPos hDenLe
  have hRadiusHalf :
      1 / (2 *
          (((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2)) <=
        1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have hCountNonneg :
        0 <= ((posWindow.ncard + negWindow.ncard : Nat) : Real) := by
      positivity
    linarith
  have hPositive :
      1 / (2 *
          (((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2)) <=
        abs (Tprime - (symmetricCompletedZeroValue p).im) := by
    by_cases hp :
        abs (center - (symmetricCompletedZeroValue p).im) < 1
    case pos =>
      have hpFinite := (hPosFinite.mem_toFinset).2 (by
        change abs (center - (symmetricCompletedZeroValue p).im) < 1
        exact hp)
      have hInside := hAvoid
        (Subtype.mk (symmetricCompletedZeroValue p).im (by
          dsimp [forbidden]
          exact Finset.mem_union.mpr (Or.inl (by
            dsimp [posOrdinates]
            exact Finset.mem_image.mpr
              (Exists.intro p (And.intro hpFinite rfl))))))
      exact hRadiusMono.trans (by simpa using hInside)
    case neg =>
      have hOutsideCenter :
          1 <= abs (center - (symmetricCompletedZeroValue p).im) :=
        le_of_not_gt hp
      have hCenterToTprime : abs (center - Tprime) <= 1 / 2 := by
        apply (abs_le).2
        exact And.intro (by
          dsimp [center]
          linarith)
          (by
            dsimp [center]
            linarith)
      have hTriangle :
          abs (center - (symmetricCompletedZeroValue p).im) <=
            abs (center - Tprime) +
              abs (Tprime - (symmetricCompletedZeroValue p).im) :=
        abs_sub_le _ _ _
      have hHalfLe :
          1 / 2 <= abs (Tprime - (symmetricCompletedZeroValue p).im) := by
        linarith
      exact hRadiusHalf.trans hHalfLe
  have hNegative :
      1 / (2 *
          (((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2)) <=
        abs ((-Tprime) - (symmetricCompletedZeroValue p).im) := by
    by_cases hp :
        abs ((-center) - (symmetricCompletedZeroValue p).im) < 1
    case pos =>
      have hpFinite := (hNegFinite.mem_toFinset).2 (by
        change abs ((-center) - (symmetricCompletedZeroValue p).im) < 1
        exact hp)
      have hInside := hAvoid
        (Subtype.mk (-(symmetricCompletedZeroValue p).im) (by
          dsimp [forbidden]
          exact Finset.mem_union.mpr (Or.inr (by
            dsimp [negOrdinates]
            exact Finset.mem_image.mpr
              (Exists.intro p (And.intro hpFinite rfl))))))
      calc
        1 / (2 *
            (((posWindow.ncard + negWindow.ncard : Nat) : Real) + 2)) <=
            abs (Tprime - (-(symmetricCompletedZeroValue p).im)) :=
          hRadiusMono.trans (by simpa using hInside)
        _ = abs ((-Tprime) - (symmetricCompletedZeroValue p).im) := by
          rw [show (-Tprime) - (symmetricCompletedZeroValue p).im =
              -(Tprime - (-(symmetricCompletedZeroValue p).im)) by ring,
            abs_neg]
    case neg =>
      have hOutsideCenter :
          1 <= abs ((-center) - (symmetricCompletedZeroValue p).im) :=
        le_of_not_gt hp
      have hCenterToTprime : abs (center - Tprime) <= 1 / 2 := by
        apply (abs_le).2
        exact And.intro (by
          dsimp [center]
          linarith)
          (by
            dsimp [center]
            linarith)
      have hNegCenterToNegTprime :
          abs ((-center) - (-Tprime)) <= 1 / 2 := by
        calc
          abs ((-center) - (-Tprime)) = abs (center - Tprime) := by
            rw [show (-center) - (-Tprime) = -(center - Tprime) by ring,
              abs_neg]
          _ <= 1 / 2 := hCenterToTprime
      have hTriangle :
          abs ((-center) - (symmetricCompletedZeroValue p).im) <=
            abs ((-center) - (-Tprime)) +
              abs ((-Tprime) - (symmetricCompletedZeroValue p).im) :=
        abs_sub_le _ _ _
      have hHalfLe :
          1 / 2 <= abs ((-Tprime) - (symmetricCompletedZeroValue p).im) := by
        linarith
      exact hRadiusHalf.trans hHalfLe
  exact And.intro hPositive hNegative

end BombieriVinogradov.SiegelWalfisz
