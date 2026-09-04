import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exhaustive logarithmic-height split

Either the large-height modulus inclusion applies, or the square-root
logarithmic height is bounded. The natural endpoint two is included.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem sqrtLog_height_split (A : Real) {x : Nat} (hx : 2 <= x) :
    Or (And (3 <= x) (16 * A ^ 2 <= Real.sqrt (Real.log x)))
      (Real.sqrt (Real.log x) <= 1 + 16 * A ^ 2) := by
  by_cases hxThree : 3 <= x
  case pos =>
    by_cases hLarge : 16 * A ^ 2 <= Real.sqrt (Real.log x)
    case pos => exact Or.inl (And.intro hxThree hLarge)
    case neg =>
      apply Or.inr
      nlinarith
  case neg =>
    have hxTwo : x = 2 :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hxThree)) hx
    subst x
    have hLog : Real.log (2 : Real) <= 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
      linarith
    have hSqrt : Real.sqrt (Real.log (2 : Real)) <= 1 := Real.sqrt_le_one.mpr hLog
    apply Or.inr
    change Real.sqrt (Real.log (2 : Real)) <= 1 + 16 * A ^ 2
    have hSquare : 0 <= A ^ 2 := by positivity
    nlinarith

end BombieriVinogradov.SiegelWalfisz
