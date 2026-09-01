import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Geometry of the Siegel Cauchy circle

This module owns the fixed metric inequalities for the circle centered at two
with radius three-halves.
-/

set_option autoImplicit false

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

/-- The fixed circle used for Cauchy's inequalities in the Siegel-product argument. -/
def siegelCauchyCircle : Set ℂ := sphere 2 (3 / 2 : ℝ)

theorem siegelCauchyCircle_re_lower {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    (1 / 2 : ℝ) ≤ s.re := by
  have hnorm : ‖s - 2‖ = (3 / 2 : ℝ) := by
    simpa [siegelCauchyCircle, mem_sphere, Complex.dist_eq] using hs
  have hre : |s.re - 2| ≤ (3 / 2 : ℝ) := by
    calc
      |s.re - 2| = |(s - 2).re| := by norm_num
      _ ≤ ‖s - 2‖ := Complex.abs_re_le_norm _
      _ = (3 / 2 : ℝ) := hnorm
  linarith [neg_abs_le (s.re - 2)]

theorem siegelCauchyCircle_norm_sub_one_lower {s : ℂ}
    (hs : s ∈ siegelCauchyCircle) : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have hdist : dist s (2 : ℂ) = (3 / 2 : ℝ) := by
    simpa only [siegelCauchyCircle, mem_sphere] using hs
  have htriangle : dist s (2 : ℂ) ≤ dist s (1 : ℂ) + dist (1 : ℂ) (2 : ℂ) :=
    dist_triangle _ _ _
  rw [hdist] at htriangle
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  rw [hone] at htriangle
  linarith

theorem siegelCauchyCircle_ne_one {s : ℂ} (hs : s ∈ siegelCauchyCircle) : s ≠ 1 := by
  intro h
  subst s
  have hbound := siegelCauchyCircle_norm_sub_one_lower hs
  norm_num at hbound

theorem siegelCauchyCircle_norm_upper {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    ‖s‖ ≤ (7 / 2 : ℝ) := by
  have hdist : dist s (2 : ℂ) = (3 / 2 : ℝ) := by
    simpa only [siegelCauchyCircle, mem_sphere] using hs
  have htriangle : dist s (0 : ℂ) ≤ dist s (2 : ℂ) + dist (2 : ℂ) (0 : ℂ) :=
    dist_triangle _ _ _
  rw [hdist] at htriangle
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  linarith

end BombieriVinogradov.SiegelWalfisz
