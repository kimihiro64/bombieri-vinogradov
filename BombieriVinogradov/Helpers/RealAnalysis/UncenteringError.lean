import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Absorption of the primitive uncentering errors

Two unit-scale corrections and the exceptional reciprocal constant fit
inside one uniform multiple of the primary-plus-secondary source scale.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem uncentering_error_le_uniform_scale
    {a b P Q : Real} (ha : 0 <= a) (hb : 0 <= b)
    (hP : 1 <= P) (hQ : 0 <= Q) :
    a * P + P + P + b * P + (4 / 3 + Q) <=
      (a + b + 4) * (P + Q) := by
  have hProduct : 0 <= (a + b + 3) * Q := by positivity
  nlinarith

end BombieriVinogradov.RealAnalysis
