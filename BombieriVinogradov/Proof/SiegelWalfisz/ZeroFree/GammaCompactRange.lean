import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Real Gamma bound on the compact initial range

This module proves the explicit bound `Gamma x <= 4` for
`1 / 4 <= x <= 2` using convexity and the Gamma recurrence.
-/

set_option autoImplicit false

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem realGamma_le_four_of_mem_quarter_two {x : ℝ}
    (hxLower : 1 / 4 ≤ x) (hxUpper : x ≤ 2) :
    Real.Gamma x ≤ 4 := by
  have hxPos : 0 < x := by linarith
  by_cases hxOne : x ≤ 1
  · have hsegment : x + 1 ∈ segment ℝ (1 : ℝ) 2 := by
      rw [segment_eq_Icc (by norm_num : (1 : ℝ) ≤ 2)]
      constructor <;> linarith
    have hnext : Real.Gamma (x + 1) ≤ 1 := by
      have hconv := Real.convexOn_Gamma.le_on_segment
        (show (1 : ℝ) ∈ Ioi 0 by norm_num)
        (show (2 : ℝ) ∈ Ioi 0 by norm_num) hsegment
      simpa [Real.Gamma_two] using hconv
    have hrecurrence := Real.Gamma_add_one hxPos.ne'
    have hgammaPos := Real.Gamma_pos_of_pos hxPos
    nlinarith
  · have hxOneLower : 1 ≤ x := le_of_not_ge hxOne
    have hsegment : x ∈ segment ℝ (1 : ℝ) 2 := by
      rw [segment_eq_Icc (by norm_num : (1 : ℝ) ≤ 2)]
      exact ⟨hxOneLower, hxUpper⟩
    have hbound := Real.convexOn_Gamma.le_on_segment
      (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Ioi 0 by norm_num) hsegment
    have hboundOne : Real.Gamma x ≤ 1 := by
      simpa [Real.Gamma_two] using hbound
    linarith

end BombieriVinogradov.SiegelWalfisz
