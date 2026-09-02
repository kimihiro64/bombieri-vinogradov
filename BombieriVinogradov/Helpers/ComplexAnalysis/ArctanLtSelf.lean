import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A strict arctangent bound

This module owns the reusable real inequality `arctan x < x` for positive `x`.
-/

set_option autoImplicit false

namespace Real

theorem arctan_lt_self_of_pos {x : Real} (hx : 0 < x) : arctan x < x := by
  have hArctanPos : 0 < arctan x := arctan_pos.mpr hx
  have hTangent := lt_tan hArctanPos (arctan_lt_pi_div_two x)
  simpa using hTangent

end Real
