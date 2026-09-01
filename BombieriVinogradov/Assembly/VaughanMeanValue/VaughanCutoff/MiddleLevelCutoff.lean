import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.MiddleLevelPowers
import Mathlib.Tactic

/-!
# Integer cutoff for the middle Vaughan level

The source parameter `X^(1/3)` is rounded upward. This module owns the natural
cutoff and the exact one-sided rounding bounds only.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

def middleLevelCutoff (X : Nat) : Nat :=
  Nat.ceil (middleLevelRoot (X : Real))

theorem middleLevelCutoff_one_le (X : Nat) (hX : 2 <= X) :
    1 <= middleLevelCutoff X := by
  apply Nat.one_le_ceil_iff.mpr
  apply middleLevelRoot_pos
  exact_mod_cast (show 0 < X by omega)

theorem middleLevelRoot_le_cutoff (X : Nat) :
    middleLevelRoot (X : Real) <= (middleLevelCutoff X : Real) := by
  exact Nat.le_ceil _

theorem middleLevelCutoff_lt_root_add_one (X : Nat) :
    (middleLevelCutoff X : Real) < middleLevelRoot (X : Real) + 1 := by
  exact Nat.ceil_lt_add_one (middleLevelRoot_nonneg (by positivity))

theorem middleLevelCutoff_le (X : Nat) (hX : 2 <= X) :
    middleLevelCutoff X <= X := by
  apply Nat.ceil_le.mpr
  apply middleLevelRoot_le_self
  exact_mod_cast (show 1 <= X by omega)

end BombieriVinogradov.VaughanMeanValue
