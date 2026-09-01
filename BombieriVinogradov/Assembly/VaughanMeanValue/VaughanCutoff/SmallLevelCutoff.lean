import Mathlib.Tactic

/-!
# Natural cutoff for the small Vaughan level

The source cutoff is exactly `Q^2`. This module owns only its natural-number
definition and feasibility under `Q^6 <= X`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.VaughanMeanValue

def smallLevelCutoff (Q : Nat) : Nat := Q ^ 2

theorem smallLevelCutoff_one_le (Q : Nat) (hQ : 1 <= Q) :
    1 <= smallLevelCutoff Q := by
  exact Nat.one_le_pow 2 Q (by omega)

theorem smallLevelCutoff_le (X Q : Nat) (hQ : 1 <= Q)
    (hqSixthX : Q ^ 6 <= X) :
    smallLevelCutoff Q <= X := by
  apply (Nat.pow_le_pow_right (by omega : 0 < Q) (by omega : 2 <= 6)).trans
  exact hqSixthX

end BombieriVinogradov.VaughanMeanValue
