import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Geometry

/-!
# Analytic neighborhood of the Siegel Cauchy circle

This module owns the fixed open disk used for locally uniform convergence of
the grouped character L-series.
-/

set_option autoImplicit false

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

/-- A fixed open disk strictly containing the source Cauchy circle. -/
def siegelAnalyticDomain : Set ℂ := ball 2 (7 / 4 : ℝ)

theorem siegelCauchyCircle_subset_analyticDomain :
    siegelCauchyCircle ⊆ siegelAnalyticDomain := by
  intro s hs
  rw [siegelCauchyCircle, mem_sphere] at hs
  rw [siegelAnalyticDomain, mem_ball]
  linarith

theorem siegelAnalyticDomain_re_lower {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    (1 / 4 : ℝ) < s.re := by
  have hnorm : ‖s - 2‖ < (7 / 4 : ℝ) := by
    simpa [siegelAnalyticDomain, mem_ball, Complex.dist_eq] using hs
  have hre : |s.re - 2| < (7 / 4 : ℝ) :=
    (Complex.abs_re_le_norm (s - 2)).trans_lt (by simpa using hnorm)
  linarith [neg_abs_le (s.re - 2)]

theorem siegelAnalyticDomain_norm_upper {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    ‖s‖ < (15 / 4 : ℝ) := by
  have hdist : dist s (2 : ℂ) < (7 / 4 : ℝ) := by
    simpa only [siegelAnalyticDomain, mem_ball] using hs
  have htriangle : dist s (0 : ℂ) ≤ dist s (2 : ℂ) + dist (2 : ℂ) (0 : ℂ) :=
    dist_triangle _ _ _
  rw [Complex.dist_eq] at hdist
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  linarith

end BombieriVinogradov.SiegelWalfisz
