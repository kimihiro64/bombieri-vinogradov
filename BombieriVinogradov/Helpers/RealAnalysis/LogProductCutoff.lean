import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic envelopes for positive natural cutoffs

One outer logarithm controls every smaller positive conductor.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A product above one has a nonnegative logarithm. -/
theorem log_mul_nat_nonneg {X : Real} {m : Nat} (hX : 1 <= X) (hm : 1 <= m) :
    0 <= Real.log (X * (m : Real)) := by
  apply Real.log_nonneg
  have hRaw : (((1 : Nat) : Real) <= (m : Real)) := Nat.cast_le.mpr hm
  have hM : (1 : Real) <= (m : Real) := by simpa only [Nat.cast_one] using hRaw
  calc
    (1 : Real) = 1 * 1 := by ring
    _ <= X * (m : Real) := by gcongr

/-- Every natural power of the logarithm is bounded at the largest positive cutoff. -/
theorem log_mul_nat_pow_le {X : Real} {m n : Nat}
    (hX : 1 <= X) (hm : 1 <= m) (hmn : m <= n) (p : Nat) :
    Real.log (X * (m : Real)) ^ p <= Real.log (X * (n : Real)) ^ p := by
  have hXPos : 0 < X := by linarith
  have hMPos : (0 : Real) < (m : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hProductPos : 0 < X * (m : Real) := by positivity
  have hProduct : X * (m : Real) <= X * (n : Real) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmn) hXPos.le
  have hLog := Real.log_le_log hProductPos hProduct
  have hNonneg := log_mul_nat_nonneg hX hm
  gcongr

end BombieriVinogradov.RealAnalysis
