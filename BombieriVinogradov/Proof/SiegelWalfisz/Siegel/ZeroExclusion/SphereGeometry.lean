import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.AnalyticDomain
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Geometry of the Cauchy sphere near one

This module proves that the small sphere centered at a real point just left of
one remains inside the analytic domain and the sharp block-bound region.
-/

set_option autoImplicit false

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def zeroExclusionRadius (N : ℕ) : ℝ :=
  1 / (16 * (1 + Real.log N))

theorem zeroExclusionRadius_pos {N : ℕ} [NeZero N] :
    0 < zeroExclusionRadius N := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  unfold zeroExclusionRadius
  positivity

theorem zeroExclusionRadius_le {N : ℕ} [NeZero N] :
    zeroExclusionRadius N ≤ 1 / 16 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hden : 0 < 16 * (1 + Real.log N) := by positivity
  unfold zeroExclusionRadius
  rw [div_le_iff₀ hden]
  nlinarith

theorem zeroExclusionSphere_geometry {N : ℕ} [NeZero N]
    {t : ℝ} (htLower : 1 - zeroExclusionRadius N ≤ t) (htUpper : t ≤ 1)
    {z : ℂ} (hz : z ∈ sphere (t : ℂ) (zeroExclusionRadius N)) :
    z ∈ siegelAnalyticDomain ∧
      1 - 1 / (8 * (1 + Real.log N)) ≤ z.re ∧
      7 / 8 ≤ z.re ∧ ‖z‖ ≤ 2 := by
  let r := zeroExclusionRadius N
  have hrPos : 0 < r := zeroExclusionRadius_pos
  have hrSmall : r ≤ 1 / 16 := zeroExclusionRadius_le
  have hzdist : dist z (t : ℂ) = r := by
    simpa [r] using (mem_sphere.mp hz)
  have hnormSub : ‖z - (t : ℂ)‖ = r := by
    simpa [Complex.dist_eq] using hzdist
  have hreAbs : |z.re - t| ≤ r := by
    have h := Complex.abs_re_le_norm (z - (t : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re, hnormSub] at h
    exact h
  have hreLower : t - r ≤ z.re := by
    linarith [neg_abs_le (z.re - t)]
  have hsharp : 1 - 1 / (8 * (1 + Real.log N)) ≤ z.re := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hNreal
    have hlogOne : Ne (1 + Real.log N) 0 := by linarith
    have hrIdentity : 2 * r = 1 / (8 * (1 + Real.log N)) := by
      dsimp [r, zeroExclusionRadius]
      field_simp
      norm_num
    linarith
  have hseven : 7 / 8 ≤ z.re := by
    linarith
  have htPos : 0 < t := by linarith
  have hnormT : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htPos]
    exact htUpper
  have hnormZ : ‖z‖ ≤ 2 := by
    calc
      ‖z‖ = ‖(z - (t : ℂ)) + (t : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (t : ℂ)‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ r + 1 := add_le_add hnormSub.le hnormT
      _ ≤ 2 := by linarith
  have hdistTTwo : dist (t : ℂ) 2 = 2 - t := by
    rw [Complex.dist_eq]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : t - 2 ≤ 0)]
    ring
  have hdist : dist z 2 < 7 / 4 := by
    calc
      dist z 2 ≤ dist z (t : ℂ) + dist (t : ℂ) 2 := dist_triangle _ _ _
      _ = r + (2 - t) := by rw [hzdist, hdistTTwo]
      _ ≤ 1 + 2 * r := by linarith
      _ < 7 / 4 := by linarith
  exact ⟨by simpa [siegelAnalyticDomain] using hdist, hsharp, hseven, hnormZ⟩

end BombieriVinogradov.SiegelWalfisz
