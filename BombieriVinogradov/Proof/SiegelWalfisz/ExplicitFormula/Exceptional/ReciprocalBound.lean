import BombieriVinogradov.Helpers.ComplexAnalysis.ReciprocalRealGap
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Reciprocal bound near the exceptional-zero endpoint

The real-part lower bound controls the nonsingular reciprocal left after
centering the exceptional-zero contribution.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_one_div_le_four_thirds_of_three_quarters_le_re
    {beta : Complex} (hLower : (3 / 4 : Real) <= beta.re) :
    norm ((1 : Complex) / beta) <= (4 / 3 : Real) := by
  have hGap : (3 / 4 : Real) / 1 <= beta.re := by
    simpa only [div_one] using hLower
  calc
    norm ((1 : Complex) / beta) <= (1 : Real) / (3 / 4) :=
      BombieriVinogradov.ComplexAnalysis.norm_one_div_le_scale_div_of_re_gap
        (by norm_num) (by norm_num) hGap
    _ = (4 / 3 : Real) := by norm_num

end BombieriVinogradov.SiegelWalfisz
