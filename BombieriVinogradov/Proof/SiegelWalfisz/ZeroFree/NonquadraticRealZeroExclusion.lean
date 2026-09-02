import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ImprimitiveComplexZeroGapBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exclusion of real exceptional zeros for nonquadratic characters

At imaginary part zero, the nonquadratic zero gap has denominator
`log N + log 2`. Shrinking its absolute constant gives a strict gap with
denominator `log N`, excluding any real exceptional zero in that region.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_nonquadratic_realZero_exclusion :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        chi ≠ 1 -> chi ^ 2 ≠ 1 ->
          forall {s : Complex}, 0 < s.re -> chi.LFunction s = 0 ->
            s.im = 0 -> c / Real.log N < 1 - s.re := by
  obtain ⟨cGap, hcGapPos, hGap⟩ :=
    exists_imprimitive_complexZero_gap
  let c : Real := cGap / 4
  have hcPos : 0 < c := div_pos hcGapPos (by norm_num)
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN chi hchi hchiSquare s hs hzero hsReal
  have hNLower :=
    BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one
      chi hchi
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  have hTwoLeN : 2 ≤ N := le_trans (by norm_num) hNLower
  have hLogTwoLe : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hTwoLeN)
  have hLogTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let D : Real := Real.log N + Real.log 2
  have hDPos : 0 < D := by
    dsimp [D]
    linarith
  have hDLe : D ≤ 2 * Real.log N := by
    dsimp [D]
    linarith
  have hQuarterNonneg : 0 ≤ cGap / 4 :=
    (div_nonneg hcGapPos.le (by norm_num))
  have hProductLe :
      (cGap / 4) * D ≤ (cGap / 4) * (2 * Real.log N) :=
    mul_le_mul_of_nonneg_left hDLe hQuarterNonneg
  have hProductStrict :
      (cGap / 4) * (2 * Real.log N) < cGap * Real.log N := by
    nlinarith [mul_pos hcGapPos hLogNPos]
  have hCross : c * D < cGap * Real.log N := by
    dsimp [c]
    exact hProductLe.trans_lt hProductStrict
  have hRatio : c / Real.log N < cGap / D :=
    (div_lt_div_iff₀ hLogNPos hDPos).2 hCross
  have hSourceGap := hGap chi hchi hchiSquare hs hzero
  have hSourceGapD : cGap / D ≤ 1 - s.re := by
    simpa [D, hsReal] using hSourceGap
  exact hRatio.trans_le hSourceGapD

end BombieriVinogradov.SiegelWalfisz
