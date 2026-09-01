import Mathlib.Analysis.Complex.Basic

/-!
# The de la Vallee Poussin trigonometric weight

This module proves the nonnegativity of the complex form of
`3 + 4 * cos(theta) + cos(2 * theta)` on the unit circle.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem re_three_add_four_mul_add_sq_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (3 + 4 * z + z ^ 2).re := by
  have hnormSq : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = 1 := by rw [hz]; norm_num
  norm_num [Complex.add_re, Complex.mul_re, pow_two]
  nlinarith [sq_nonneg (z.re + 1)]

end BombieriVinogradov.SiegelWalfisz
