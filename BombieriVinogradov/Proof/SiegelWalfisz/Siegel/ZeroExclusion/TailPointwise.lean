import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailBlock

/-!
# Shifted pointwise character-block estimate

This module specializes the positive-index block theorem to the tail index
`k + 1` used by the scalar comparison series.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_tail_shifted_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {s : ℂ}
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re)
    (hseven : 7 / 8 ≤ s.re) (hnorm : ‖s‖ ≤ 2) (k : ℕ) :
    ‖characterLBlock chi (k + 1) s‖ ≤
      2 * Real.exp (1 / 8 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-15 / 8 : ℝ) :=
  norm_characterLBlock_tail_near_one_le chi hchi (Nat.le_add_left 1 k)
    hre hseven hnorm

end BombieriVinogradov.SiegelWalfisz
