import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Real part of the doubled-height pole kernel

This module evaluates the real part of the zeta pole term at
`sigma + 2 i t`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem doubledHeightPole_re (sigma t : Real) :
    (1 / (((sigma : Complex) + 2 * Complex.I * t) - 1)).re =
      (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end BombieriVinogradov.SiegelWalfisz
