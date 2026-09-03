import BombieriVinogradov.Helpers.RealAnalysis.FiniteSetIntervalAvoidance
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Selecting a height away from every completed zero

This module specializes finite-set interval avoidance to the ordinates of
completed zeros. It keeps the separation in terms of the actual centered
window cardinality; logarithmic normalization belongs to a later module.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- A height in the next unit interval can be chosen uniformly away from every
completed zero, with an explicit gap governed by the actual nearby-window
cardinality. -/
theorem exists_zeroHeight_separated_by_ncard
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) :
    exists Tprime : Real, And (T <= Tprime)
      (And (Tprime <= T + 1)
        (forall p : SymmetricCompletedZeroIndex chi,
          1 / (2 *
            (((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard : Real) + 2)) <=
              abs (Tprime - (symmetricCompletedZeroValue p).im))) := by
  classical
  let center : Real := T + 1 / 2
  let window : Set (SymmetricCompletedZeroIndex chi) :=
    zeroHeightWindow (chi := chi) center
  have hFinite : Set.Finite window := by
    simpa [window, center] using
      finite_zeroHeightWindow hchi hPrimitive (T + 1 / 2)
  let ordinates : Finset Real :=
    hFinite.toFinset.image (fun p => (symmetricCompletedZeroValue p).im)
  choose Tprime hTprimeLower hTprimeUpper hAvoid using
    BombieriVinogradov.RealAnalysis.exists_unitInterval_away_from_finset
      ordinates T
  refine Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper ?_))
  intro p
  change 1 / (2 * ((window.ncard : Real) + 2)) <=
    abs (Tprime - (symmetricCompletedZeroValue p).im)
  have hImageCardLe : ordinates.card <= window.ncard := by
    calc
      ordinates.card <= hFinite.toFinset.card := by
        dsimp [ordinates]
        exact Finset.card_image_le
      _ = window.ncard := by
        symm
        exact Set.ncard_eq_toFinset_card window hFinite
  have hImageCardCast :
      (ordinates.card : Real) <= (window.ncard : Real) :=
    (Nat.cast_le).2 hImageCardLe
  have hSmallDenPos : 0 < 2 * ((ordinates.card : Real) + 2) := by
    positivity
  have hDenLe :
      2 * ((ordinates.card : Real) + 2) <=
        2 * ((window.ncard : Real) + 2) := by
    linarith
  have hRadiusMono :
      1 / (2 * ((window.ncard : Real) + 2)) <=
        1 / (2 * ((ordinates.card : Real) + 2)) :=
    one_div_le_one_div_of_le hSmallDenPos hDenLe
  by_cases hp : abs (center - (symmetricCompletedZeroValue p).im) < 1
  case pos =>
    have hpFinite := (hFinite.mem_toFinset).2 (by
      change abs (center - (symmetricCompletedZeroValue p).im) < 1
      exact hp)
    have hInside := hAvoid
      (Subtype.mk (symmetricCompletedZeroValue p).im (by
        dsimp [ordinates]
        exact Finset.mem_image.mpr
          (Exists.intro p (And.intro hpFinite rfl))))
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
    have hRadiusHalf :
        1 / (2 * ((window.ncard : Real) + 2)) <= 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by
        have hNcardNonneg : 0 <= (window.ncard : Real) := by
          positivity
        linarith)
    exact hRadiusHalf.trans hHalfLe

end BombieriVinogradov.SiegelWalfisz
