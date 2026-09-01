import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValuePositivity
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueReality
import Mathlib.Topology.Order.IntermediateValue

/-!
# Positivity propagated through a zero-free interval

This module turns positivity at one into positivity at a nearby real point
when a quadratic L-function has no zero between those points.
-/

set_option autoImplicit false

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 → chi.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  let f : ℝ → ℝ := fun t ↦ (chi.LFunction t).re
  have hfcont : Continuous f := by
    exact Complex.continuous_re.comp
      ((chi.differentiable_LFunction hchi).continuous.comp Complex.continuous_ofReal)
  have hone : 0 < f 1 := quadraticLFunction_one_re_pos chi hchiSquare hchi
  by_contra hnot
  have himS := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hfs_ne : f s ≠ 0 := by
    intro hfs
    apply hnozero s le_rfl hsUpper.le
    apply Complex.ext
    · simpa [f] using hfs
    · simpa using himS
  have hfsNeg : f s < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hfs_ne
  have hzeroMem : 0 ∈ Icc (f s) (f 1) := ⟨hfsNeg.le, hone.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hsUpper.le hfcont.continuousOn hzeroMem
  have himT := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain (hsLower.trans ht.1) ht.2)
  apply hnozero t ht.1 ht.2
  apply Complex.ext
  · simpa [f] using hft
  · simpa using himT

end BombieriVinogradov.SiegelWalfisz
