import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Avoiding a finite set inside a unit interval

This module uses an interior grid and the finite pigeonhole principle to find
a point in a unit interval with explicit separation from every member of a
finite set of real numbers.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A finite set of real numbers can be avoided inside every unit interval
with separation at least one over twice its cardinality plus two. -/
theorem exists_unitInterval_away_from_finset
    (s : Finset Real) (T : Real) :
    exists t : Real, And (T <= t)
      (And (t <= T + 1)
        (forall x : s,
          1 / (2 * ((s.card : Real) + 2)) <= abs (t - (x : Real)))) := by
  classical
  let denominator : Real := (s.card : Real) + 2
  let radius : Real := 1 / (2 * denominator)
  let grid : Fin (s.card + 1) -> Real := fun k =>
    T + ((k.val + 1 : Nat) : Real) / denominator
  have hDenPos : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hGridLower : forall k : Fin (s.card + 1), T <= grid k := by
    intro k
    have hNumNonneg : 0 <= ((k.val + 1 : Nat) : Real) := by
      positivity
    have hFracNonneg :
        0 <= ((k.val + 1 : Nat) : Real) / denominator :=
      div_nonneg hNumNonneg (le_of_lt hDenPos)
    dsimp [grid]
    linarith
  have hGridUpper : forall k : Fin (s.card + 1), grid k <= T + 1 := by
    intro k
    have hkNat : k.val + 1 <= s.card + 2 :=
      Nat.le_trans (Nat.succ_le_iff.mpr k.isLt)
        (Nat.le_succ (s.card + 1))
    have hkCast : ((k.val + 1 : Nat) : Real) <= denominator := by
      have hkCastRaw :
          ((k.val + 1 : Nat) : Real) <= ((s.card + 2 : Nat) : Real) :=
        (Nat.cast_le).2 hkNat
      simpa [denominator] using hkCastRaw
    have hFracLe :
        ((k.val + 1 : Nat) : Real) / denominator <= 1 :=
      (div_le_one hDenPos).2 hkCast
    dsimp [grid]
    linarith
  by_cases hGood : exists k : Fin (s.card + 1),
      forall x : s, radius <= abs (grid k - (x : Real))
  case pos =>
    choose k hk using hGood
    exact Exists.intro (grid k)
      (And.intro (hGridLower k)
        (And.intro (hGridUpper k) (by
          intro x
          simpa [radius, denominator] using hk x)))
  case neg =>
    have hBad : forall k : Fin (s.card + 1),
        exists x : s, abs (grid k - (x : Real)) < radius := by
      intro k
      by_contra hNone
      apply hGood
      exact Exists.intro k (fun x =>
        le_of_not_gt (fun hx => hNone (Exists.intro x hx)))
    let chosen : Fin (s.card + 1) -> s := fun k =>
      Classical.choose (hBad k)
    have hChosen : forall k : Fin (s.card + 1),
        abs (grid k - (chosen k : Real)) < radius := by
      intro k
      exact Classical.choose_spec (hBad k)
    have hCard :
        Fintype.card s < Fintype.card (Fin (s.card + 1)) := by
      simp
    have hCollision : exists k l,
        And (Ne k l) (chosen k = chosen l) :=
      Fintype.exists_ne_map_eq_of_card_lt chosen hCard
    choose k l hkl hEq using hCollision
    have hCloseRight :
        abs ((chosen k : Real) - grid l) < radius := by
      have hl := hChosen l
      rw [abs_sub_comm] at hl
      simpa [hEq] using hl
    have hClose : abs (grid k - grid l) < 2 * radius := by
      calc
        abs (grid k - grid l) <=
            abs (grid k - (chosen k : Real)) +
              abs ((chosen k : Real) - grid l) :=
          abs_sub_le _ _ _
        _ < radius + radius :=
          add_lt_add (hChosen k) hCloseRight
        _ = 2 * radius := by ring
    have hValNe : Ne k.val l.val := by
      intro hVal
      exact hkl (Fin.ext hVal)
    have hIndexGap :
        (1 : Real) <= abs ((k.val : Real) - (l.val : Real)) :=
      Or.elim (lt_or_gt_of_ne hValNe)
        (fun hlt => by
          have hNat : k.val + 1 <= l.val :=
            Nat.succ_le_iff.mpr hlt
          have hCast : (k.val : Real) + 1 <= (l.val : Real) := by
            have hCastRaw :
                ((k.val + 1 : Nat) : Real) <= (l.val : Real) :=
              (Nat.cast_le).2 hNat
            simpa using hCastRaw
          rw [abs_of_nonpos (by linarith)]
          linarith)
        (fun hgt => by
          have hNat : l.val + 1 <= k.val :=
            Nat.succ_le_iff.mpr hgt
          have hCast : (l.val : Real) + 1 <= (k.val : Real) := by
            have hCastRaw :
                ((l.val + 1 : Nat) : Real) <= (k.val : Real) :=
              (Nat.cast_le).2 hNat
            simpa using hCastRaw
          rw [abs_of_nonneg (by linarith)]
          linarith)
    have hGridDifference :
        grid k - grid l =
          ((k.val : Real) - (l.val : Real)) * (1 / denominator) := by
      dsimp [grid]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    have hGridGap : 1 / denominator <= abs (grid k - grid l) := by
      rw [hGridDifference, abs_mul, abs_of_pos (by positivity :
        0 < (1 / denominator))]
      simpa using
        mul_le_mul_of_nonneg_right hIndexGap
          (le_of_lt (show 0 < 1 / denominator by positivity))
    have hTwiceRadius : 2 * radius = 1 / denominator := by
      dsimp [radius]
      field_simp
    linarith

end BombieriVinogradov.RealAnalysis
