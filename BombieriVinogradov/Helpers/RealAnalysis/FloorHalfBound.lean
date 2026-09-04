import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A quantitative positive natural floor bound

Above two, the natural floor lies between half the input and the input.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- The natural floor of a real input above two is a positive half-size cutoff. -/
theorem floor_half_bounds {T : Real} (hT : 2 <= T) :
    And (1 <= Nat.floor T)
      (And ((Nat.floor T : Real) <= T) (T / 2 <= (Nat.floor T : Real))) := by
  have hOne : (1 : Real) <= T := by linarith
  have hRaw : (((1 : Nat) : Real) <= T) := by simpa only [Nat.cast_one] using hOne
  have hUpper : (Nat.floor T : Real) <= T := Nat.floor_le (show 0 <= T by linarith)
  refine And.intro (Nat.le_floor hRaw) (And.intro hUpper ?_)
  have hFloor := Nat.lt_floor_add_one T
  linarith

end BombieriVinogradov.RealAnalysis
