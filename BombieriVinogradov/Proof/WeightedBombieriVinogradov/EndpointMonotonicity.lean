import BombieriVinogradov.Definitions.WeightedDiscrepancy
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Units

/-!
# Endpoint Monotonicity

This focused module owns one bounded-endpoint responsibility.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The maximal discrepancy is nonnegative at every endpoint and modulus. -/
theorem maximalWeightedDiscrepancy_nonneg (X : Real) (q : Nat) :
    0 <= maximalWeightedDiscrepancy X q := by
  unfold maximalWeightedDiscrepancy
  let F : Units (ZMod q) -> Real := fun a =>
    iSup (fun z : Fin (Nat.floor X + 1) =>
      abs (psiProgression z.val q (a : ZMod q) -
        psiGlobal z.val / (q.totient : Real)))
  change 0 <= iSup F
  let H : Fin (Nat.floor X + 1) -> Real := fun z =>
    abs (psiProgression z.val q (1 : ZMod q) -
      psiGlobal z.val / (q.totient : Real))
  let y : Fin (Nat.floor X + 1) := Fin.last (Nat.floor X)
  have hAbs : 0 <= H y := by
    dsimp [H]
    exact abs_nonneg _
  have hH : 0 <= iSup H :=
    hAbs.trans (le_ciSup (Set.finite_range H).bddAbove y)
  have hFH : F 1 = iSup H := by rfl
  calc
    0 <= iSup H := hH
    _ = F 1 := hFH.symm
    _ <= iSup F := le_ciSup (Set.finite_range F).bddAbove 1

/-- Enlarging the real endpoint only enlarges the finite maximal domain. -/
theorem maximalWeightedDiscrepancy_mono {X M : Real} (q : Nat)
    (hFloor : Nat.floor X <= Nat.floor M) :
    maximalWeightedDiscrepancy X q <= maximalWeightedDiscrepancy M q := by
  unfold maximalWeightedDiscrepancy
  let F : Units (ZMod q) -> Real := fun a =>
    iSup (fun y : Fin (Nat.floor X + 1) =>
      abs (psiProgression y.val q (a : ZMod q) -
        psiGlobal y.val / (q.totient : Real)))
  let G : Units (ZMod q) -> Real := fun a =>
    iSup (fun z : Fin (Nat.floor M + 1) =>
      abs (psiProgression z.val q (a : ZMod q) -
        psiGlobal z.val / (q.totient : Real)))
  change iSup F <= iSup G
  refine ciSup_le (fun a => ?_)
  have hInner : F a <= G a := by
    let H : Fin (Nat.floor M + 1) -> Real := fun z =>
      abs (psiProgression z.val q (a : ZMod q) -
        psiGlobal z.val / (q.totient : Real))
    change iSup (fun y : Fin (Nat.floor X + 1) =>
      abs (psiProgression y.val q (a : ZMod q) -
        psiGlobal y.val / (q.totient : Real))) <= iSup H
    refine ciSup_le (fun y => ?_)
    let z : Fin (Nat.floor M + 1) :=
      { val := y.val
        isLt := lt_of_lt_of_le y.isLt (Nat.add_le_add_right hFloor 1) }
    exact le_ciSup_of_le (Set.finite_range H).bddAbove z (le_refl _)
  exact hInner.trans (le_ciSup (Set.finite_range G).bddAbove a)

end BombieriVinogradov.WeightedBombieriVinogradov
