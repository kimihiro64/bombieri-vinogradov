import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Reciprocal kernel of a conjugate zero pair

This algebraic identity is the exact kernel appearing in Strombergsson
equation (410).
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem conjugatePairKernel_re (sigma : Real) (rho : Complex) :
    (1 / ((sigma : Complex) - rho)).re +
      (1 / ((sigma : Complex) - (starRingEnd Complex) rho)).re =
        2 * (sigma - rho.re) /
          ((sigma - rho.re) ^ 2 + rho.im ^ 2) := by
  simp only [one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

end BombieriVinogradov.SiegelWalfisz
