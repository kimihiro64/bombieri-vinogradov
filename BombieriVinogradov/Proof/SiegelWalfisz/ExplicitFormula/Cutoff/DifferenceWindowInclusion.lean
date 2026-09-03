import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.DifferenceOrdinateBounds
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindow
import Mathlib.Tactic.Linarith

/-!
# Two-sided windows for newly retained zeros

This module places each cutoff-difference index in the positive or negative
unit-height zero window around the old cutoff.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem mem_zeroHeightWindow_or_neg_of_mem_cutoffDifference
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T Tprime : Real} {exceptional : Option Complex}
    (hTop : Tprime <= T + 1)
    {p : SymmetricCompletedZeroIndex chi}
    (hp :
      (retainedCriticalZeroCutoffDifference chi T Tprime exceptional :
        Set (SymmetricCompletedZeroIndex chi)) p) :
    Or
      (zeroHeightWindow (chi := chi) (T + 1 / 2) p)
      (zeroHeightWindow (chi := chi) (-(T + 1 / 2)) p) := by
  let y := (symmetricCompletedZeroValue p).im
  have hBoundsY :
      And (T <= abs y) (abs y < Tprime) := by
    simpa [y] using
      abs_im_bounds_of_mem_retainedCriticalZeroCutoffDifference hp
  have hUpperAbs : abs y < T + 1 :=
    lt_of_lt_of_le hBoundsY.2 hTop
  exact Or.elim (le_total 0 y)
    (fun hy => by
      have hLower : T <= y := by
        simpa [abs_of_nonneg hy] using hBoundsY.1
      have hUpper : y < T + 1 := by
        simpa [abs_of_nonneg hy] using hUpperAbs
      apply Or.inl
      change abs ((T + 1 / 2) - y) < 1
      exact (abs_lt).2
        (And.intro (by linarith) (by linarith)))
    (fun hy => by
      have hLower : T <= -y := by
        simpa [abs_of_nonpos hy] using hBoundsY.1
      have hUpper : -y < T + 1 := by
        simpa [abs_of_nonpos hy] using hUpperAbs
      apply Or.inr
      change abs (-(T + 1 / 2) - y) < 1
      exact (abs_lt).2
        (And.intro (by linarith) (by linarith)))

end BombieriVinogradov.SiegelWalfisz
