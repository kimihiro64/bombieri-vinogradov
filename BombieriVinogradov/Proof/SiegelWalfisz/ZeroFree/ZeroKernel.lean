import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Reciprocal kernels contributed by L-function zeros

This module proves the sign and vertical-alignment identities for the real
part of `(s - rho)⁻¹` used in explicit logarithmic-derivative estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- A zero with real part at most one contributes nonnegatively to the
reciprocal kernel evaluated strictly to the right of one. -/
theorem zeroKernel_re_nonneg {s rho : ℂ}
    (hs : 1 < s.re) (hrho : rho.re ≤ 1) :
    0 ≤ ((s - rho)⁻¹).re := by
  rw [Complex.inv_re, Complex.sub_re]
  exact div_nonneg (sub_nonneg.mpr (hrho.trans hs.le))
    (Complex.normSq_nonneg (s - rho))

/-- When `s` and `rho` have the same imaginary part, the reciprocal kernel is
exactly the reciprocal horizontal distance. -/
theorem zeroKernel_re_of_same_im {s rho : ℂ}
    (hre : Ne s.re rho.re) (him : s.im = rho.im) :
    ((s - rho)⁻¹).re = (s.re - rho.re)⁻¹ := by
  rw [Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    him, sub_self, mul_zero, add_zero]
  field_simp [sub_ne_zero.mpr hre]

end BombieriVinogradov.SiegelWalfisz
