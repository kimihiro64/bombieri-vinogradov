import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.UpperLevelRatio
import Mathlib.Tactic

/-!
# Integer cutoff for the upper inner Vaughan level

The source ratio `X/Q^2` is rounded upward. This module owns only the natural
cutoff and its one-sided rounding and feasibility bounds.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

def upperLevelCutoff (X Q : Nat) : Nat :=
  Nat.ceil (upperLevelRatio (X : Real) (Q : Real))

theorem upperLevelCutoff_one_le (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    1 <= upperLevelCutoff X Q := by
  apply Nat.one_le_ceil_iff.mpr
  apply upperLevelRatio_pos
  · exact_mod_cast (show 0 < X by omega)
  · exact_mod_cast (show 0 < Q by omega)

theorem upperLevelRatio_le_cutoff (X Q : Nat) :
    upperLevelRatio (X : Real) (Q : Real) <= (upperLevelCutoff X Q : Real) := by
  exact Nat.le_ceil _

theorem upperLevelCutoff_lt_ratio_add_one (X Q : Nat) :
    (upperLevelCutoff X Q : Real) <
      upperLevelRatio (X : Real) (Q : Real) + 1 := by
  exact Nat.ceil_lt_add_one (upperLevelRatio_nonneg (by positivity))

theorem upperLevelCutoff_le (X Q : Nat) (hQ : 1 <= Q) :
    upperLevelCutoff X Q <= X := by
  apply Nat.ceil_le.mpr
  apply upperLevelRatio_le_self
  · positivity
  · exact_mod_cast hQ

end BombieriVinogradov.VaughanMeanValue
