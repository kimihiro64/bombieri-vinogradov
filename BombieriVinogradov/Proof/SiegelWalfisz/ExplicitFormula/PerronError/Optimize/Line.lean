import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Definitions

/-!
# Bounds for the optimized Perron line

This module proves the logarithmic lower bound and the interval properties of
the optimized real part for every natural `x > 2`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For natural `x > 2`, `log x` is at least one. -/
theorem one_le_log_natCast {x : Nat} (hx : 2 < x) :
    (1 : Real) <= Real.log (x : Real) := by
  have hLogThree := Real.le_log_one_add_of_nonneg
    (x := (2 : Real)) (by norm_num)
  norm_num at hLogThree
  have hxThree : (3 : Real) <= (x : Real) := by exact_mod_cast hx
  exact hLogThree.trans (Real.log_le_log (by norm_num) hxThree)

/-- The optimized line lies strictly to the right of one. -/
theorem optimizedPerronLine_gt_one {x : Nat} (hx : 2 < x) :
    1 < optimizedPerronLine x := by
  have hLogPos : 0 < Real.log (x : Real) :=
    lt_of_lt_of_le zero_lt_one (one_le_log_natCast hx)
  have hInvPos : 0 < 1 / Real.log (x : Real) := by positivity
  unfold optimizedPerronLine
  linarith

/-- The optimized line is at most two, hence belongs to the full source range. -/
theorem optimizedPerronLine_le_two {x : Nat} (hx : 2 < x) :
    optimizedPerronLine x <= 2 := by
  have hLog := one_le_log_natCast hx
  have hInv : 1 / Real.log (x : Real) <= 1 := by
    have h := one_div_le_one_div_of_le zero_lt_one hLog
    norm_num at h
    simpa only [one_div] using h
  unfold optimizedPerronLine
  linarith

end BombieriVinogradov.SiegelWalfisz
