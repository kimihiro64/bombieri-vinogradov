import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.FarLog
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.HarmonicRange

/-!
# Harmonic growth in the central Perron range

This module converts the harmonic factor into one additional logarithm at the
common argument `2 * x` used by both central ranges.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For natural `x > 2`, the logarithm at `2 * x` is at least one. -/
theorem one_le_log_two_mul {x : Nat} (hx : 2 < x) :
    (1 : Real) <= Real.log (2 * (x : Real)) := by
  have hLogThree := Real.le_log_one_add_of_nonneg
    (x := (2 : Real)) (by norm_num)
  norm_num at hLogThree
  have hThree : (3 : Real) <= 2 * (x : Real) := by
    have hxThree : 3 <= x := hx
    exact_mod_cast (show 3 <= 2 * x by omega)
  exact hLogThree.trans (Real.log_le_log (by norm_num) hThree)

/-- The harmonic number is at most three times `log (2 * x)`. -/
theorem harmonic_le_three_log_two_mul
    {x : Nat} (hx : 0 < x) :
    (harmonic x : Real) <= 3 * Real.log (2 * (x : Real)) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hLogMono : Real.log (x : Real) <= Real.log (2 * (x : Real)) := by
    apply Real.log_le_log hxReal
    nlinarith [hxReal]
  have hTwoLe : (2 : Real) <= 2 * (x : Real) := by exact_mod_cast
    (show 2 <= 2 * x by omega)
  have hHalf : (1 / 2 : Real) <= Real.log (2 * (x : Real)) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) hTwoLe)
  have hHarmonic : (harmonic x : Real) <= 1 + Real.log (x : Real) :=
    harmonic_le_one_add_log x
  linarith

end BombieriVinogradov.SiegelWalfisz
