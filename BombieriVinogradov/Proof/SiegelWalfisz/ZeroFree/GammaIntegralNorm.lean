import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Norm bound for the complex Gamma function

This module bounds `norm (Gamma s)` by the real Gamma function at `re s`
directly from Euler's integral on the positive half-plane.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_Gamma_le_realGamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  calc
    ‖∫ x in Ioi (0 : ℝ), ((-x).exp : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Ioi (0 : ℝ),
          ‖((-x).exp : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0 : ℝ),
          Real.exp (-x) * x ^ (s.re - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ =
        Real.exp (-x) * x ^ (s.re - 1)
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

end BombieriVinogradov.SiegelWalfisz
