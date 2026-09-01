import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ZetaSign

/-!
# A comparison point to the left of the zeta pole

This module chooses a point that remains above the requested lower endpoint
and lies in the interval where the real Riemann zeta function is negative.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_siegelComparisonPoint {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ s : ℝ, lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧ (riemannZeta s).re < 0 := by
  obtain ⟨eta, heta, hzeta⟩ := exists_riemannZeta_neg_left
  let s := max lower (1 - eta / 2)
  have hlowerS : lower ≤ s := le_max_left _ _
  have hsevenS : 7 / 8 ≤ s := hlower.trans hlowerS
  have hsUpper : s < 1 := by
    apply max_lt hupper
    linarith
  have hetaS : 1 - eta < s := by
    have : 1 - eta < 1 - eta / 2 := by linarith
    exact this.trans_le (le_max_right _ _)
  exact ⟨s, hlowerS, hsevenS, hsUpper, hzeta s hetaS hsUpper⟩

end BombieriVinogradov.SiegelWalfisz
