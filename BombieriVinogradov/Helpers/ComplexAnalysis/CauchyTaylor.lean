import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy bounds for normalized Taylor coefficients

This module packages Cauchy's derivative estimate in the factorial-normalized form used by power series.
-/

set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

/-- The factorial-normalized iterated derivative at a center. -/
noncomputable def taylorCoefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial : ℂ)

/-- Cauchy's estimate in normalized Taylor-coefficient form. -/
theorem norm_taylorCoefficient_le {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (n : ℕ) (hR : 0 < R) (hf : Differentiable ℂ f)
    (hC : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) :
    ‖taylorCoefficient f c n‖ ≤ C / R ^ n := by
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf.diffContOnCl hC
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  rw [taylorCoefficient, norm_div]
  simp only [norm_natCast]
  calc
    ‖iteratedDeriv n f c‖ / n.factorial ≤
        (n.factorial * C / R ^ n) / n.factorial :=
      (div_le_div_iff_of_pos_right hfac).2 hderiv
    _ = C / R ^ n := by
      field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.ComplexAnalysis
