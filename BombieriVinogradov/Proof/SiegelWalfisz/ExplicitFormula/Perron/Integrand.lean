import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Analytic facts for the Perron integrand

This module owns the exponential form, right-half-plane holomorphy, and exact
norm of the scalar unsmoothed Perron integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For a positive real base, the Perron power has the ordinary real-logarithm
exponential form. -/
theorem perronKernelIntegrand_eq_exp {y : Real} (hy : 0 < y) (s : Complex) :
    perronKernelIntegrand y s =
      Complex.exp ((Real.log y : Complex) * s) / s := by
  rw [perronKernelIntegrand,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [Complex.ofReal_log hy.le]

/-- The Perron integrand is holomorphic throughout the open right half-plane. -/
theorem holomorphicOn_perronKernelIntegrand {y : Real} (hy : 0 < y) :
    HolomorphicOn (perronKernelIntegrand y) {s : Complex | 0 < s.re} := by
  intro s hs
  have hsne : Ne s 0 := by
    intro hzero
    subst s
    simp at hs
  have hEq :
      perronKernelIntegrand y =
        fun z : Complex => Complex.exp ((Real.log y : Complex) * z) / z := by
    funext z
    exact perronKernelIntegrand_eq_exp hy z
  rw [hEq]
  fun_prop

/-- The norm of the Perron integrand depends only on the real part of the
exponent and the distance to its pole. -/
theorem norm_perronKernelIntegrand {y : Real} (hy : 0 < y) (s : Complex) :
    norm (perronKernelIntegrand y s) = y ^ s.re / norm s := by
  rw [perronKernelIntegrand, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]

end BombieriVinogradov.SiegelWalfisz
