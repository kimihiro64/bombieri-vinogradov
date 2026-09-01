import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Values
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Order.IntermediateValue

/-!
# Positivity of quadratic Dirichlet L-values at one

This module proves that the value at one of a nonprincipal quadratic complex
Dirichlet character is a positive real number.
-/

set_option autoImplicit false

open Filter LSeries Set

namespace BombieriVinogradov.SiegelWalfisz

private theorem quadraticLFunction_im_eq_zero_of_one_lt {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1)
    {x : ℝ} (hx : 1 < x) : (chi.LFunction x).im = 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)]
  rw [LSeries, Complex.im_tsum (chi.LSeriesSummable_of_one_lt_re (by simpa using hx))]
  convert tsum_zero with n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    rcases quadraticValue_cases chi hchi n with hzero | hone | hneg
    · simp [hzero]
    · rw [hone, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    · rw [hneg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp

private theorem quadraticLFunction_im_eq_zero_at_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    (chi.LFunction 1).im = 0 := by
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).im
  have hLcont : ContinuousAt chi.LFunction (1 : ℂ) :=
    (chi.differentiableAt_LFunction 1 (.inr hchi_ne)).continuousAt
  have hLreal : ContinuousAt (fun x : ℝ ↦ chi.LFunction x) 1 :=
    hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hfcont : ContinuousAt f 1 :=
    Complex.continuous_im.continuousAt.comp' hLreal
  have hlimit : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds (f 1)) :=
    hfcont.mono_left inf_le_left
  have hzero : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadraticLFunction_im_eq_zero_of_one_lt chi hchi hx).symm
  exact tendsto_nhds_unique hlimit hzero

/-- A nonprincipal quadratic Dirichlet character has positive real L-value at one. -/
theorem quadraticLFunction_one_re_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    0 < (chi.LFunction 1).re := by
  have habs : LSeries.abscissaOfAbsConv (chi ·) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) chi]
    exact EReal.coe_lt_top 1
  have hseries : Tendsto (fun x : ℝ ↦ LSeries (chi ·) x) atTop (nhds 1) := by
    simpa using LSeries.tendsto_atTop habs
  have hL : Tendsto (fun x : ℝ ↦ chi.LFunction x) atTop (nhds 1) := by
    apply hseries.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)).symm
  have hre : Tendsto (fun x : ℝ ↦ (chi.LFunction x).re) atTop (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp hL using 1 <;>
      simp [Function.comp_def]
  have heventuallyPos : ∀ᶠ x : ℝ in atTop, 0 < (chi.LFunction x).re :=
    hre (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨X, hXpos, hXone⟩ :=
    (heventuallyPos.and (eventually_gt_atTop (a := (1 : ℝ)))).exists
  by_contra hnot
  have himOne := quadraticLFunction_im_eq_zero_at_one chi hchi hchi_ne
  have hreOne_ne : (chi.LFunction 1).re ≠ 0 := by
    intro hreOne
    apply chi.LFunction_apply_one_ne_zero hchi_ne
    apply Complex.ext
    · simpa using hreOne
    · simpa using himOne
  have hreOne_neg : (chi.LFunction 1).re < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hreOne_ne
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).re
  have hfcont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hLcont : ContinuousAt chi.LFunction (x : ℂ) :=
      (chi.differentiable_LFunction hchi_ne).continuous.continuousAt
    have hLreal : ContinuousAt (fun y : ℝ ↦ chi.LFunction y) x :=
      hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt rfl
    exact Complex.continuous_re.continuousAt.comp' hLreal
  have hzeroMem : 0 ∈ Icc (f 1) (f X) := ⟨hreOne_neg.le, hXpos.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hXone.le hfcont.continuousOn hzeroMem
  have himY : (chi.LFunction y).im = 0 := by
    rcases hy.1.eq_or_lt with rfl | hylt
    · exact himOne
    · exact quadraticLFunction_im_eq_zero_of_one_lt chi hchi hylt
  have hLy : chi.LFunction y = 0 := by
    apply Complex.ext
    · simpa [f] using hfy
    · simpa using himY
  exact chi.LFunction_ne_zero_of_one_le_re (.inl hchi_ne) (by simpa using hy.1) hLy

theorem norm_quadraticLFunction_one_eq_re {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    ‖chi.LFunction 1‖ = (chi.LFunction 1).re := by
  have him := quadraticLFunction_im_eq_zero_at_one chi hchi hchi_ne
  have hre := quadraticLFunction_one_re_pos chi hchi hchi_ne
  rw [Complex.norm_def, Complex.normSq_apply, him]
  norm_num [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hre]

end BombieriVinogradov.SiegelWalfisz
