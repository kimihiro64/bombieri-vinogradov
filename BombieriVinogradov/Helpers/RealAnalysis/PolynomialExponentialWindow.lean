import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial loss on a bounded height interval

The exponential rate remains fixed while only the interval-dependent
coefficient changes.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem sq_le_exp_window {a t T : Real}
    (ha : 0 <= a) (ht : 0 <= t) (h : t <= T) :
    t ^ 2 <= (T ^ 2 * Real.exp (a * T)) * Real.exp (-(a * t)) := by
  have hExp : 1 <= Real.exp (a * T) * Real.exp (-(a * t)) := by
    rw [<- Real.exp_add, <- Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    t ^ 2 <= T ^ 2 := by gcongr
    _ = T ^ 2 * 1 := by ring
    _ <= T ^ 2 * (Real.exp (a * T) * Real.exp (-(a * t))) :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = (T ^ 2 * Real.exp (a * T)) * Real.exp (-(a * t)) := by ring

end BombieriVinogradov.RealAnalysis
