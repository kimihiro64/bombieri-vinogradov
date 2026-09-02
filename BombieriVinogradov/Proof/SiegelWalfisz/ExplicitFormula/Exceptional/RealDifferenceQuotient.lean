import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real reflected-zero difference quotient

This module proves the elementary real estimate that absorbs the reflected
exceptional-zero term into the quarter-power logarithmic error scale.
-/
set_option autoImplicit false

open Set

namespace BombieriVinogradov.SiegelWalfisz

/-- A positive rpow difference quotient with exponent at most one quarter is
bounded by the quarter-power logarithmic scale. -/
theorem rpow_sub_one_div_le_quarterPower_mul_log
    {x delta : Real} (hx : 1 <= x) (hdeltaPos : 0 < delta)
    (hdeltaUpper : delta <= (1 / 4 : Real)) :
    (x ^ delta - 1) / delta <= x ^ (1 / 4 : Real) * Real.log x := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hlogNonneg : 0 <= Real.log x := Real.log_nonneg hx
  have hderiv (t : Real) (ht : (Set.Icc 0 delta) t) :
      HasDerivWithinAt (fun u : Real => x ^ u)
        (Real.log x * x ^ t) (Set.Icc 0 delta) t := by
    simpa using ((hasDerivAt_id t).const_rpow hxPos).hasDerivWithinAt
  have hbound (t : Real) (ht : (Set.Icc 0 delta) t) :
      norm (Real.log x * x ^ t) <= x ^ (1 / 4 : Real) * Real.log x := by
    have hpow : x ^ t <= x ^ (1 / 4 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hx (ht.2.trans hdeltaUpper)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hlogNonneg (Real.rpow_nonneg hxPos.le t))]
    calc
      Real.log x * x ^ t <= Real.log x * x ^ (1 / 4 : Real) :=
        mul_le_mul_of_nonneg_left hpow hlogNonneg
      _ = x ^ (1 / 4 : Real) * Real.log x := mul_comm _ _
  have hmv :=
    (convex_Icc 0 delta).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (left_mem_Icc.mpr hdeltaPos.le)
        (right_mem_Icc.mpr hdeltaPos.le)
  have hxpow : 1 <= x ^ delta := Real.one_le_rpow hx hdeltaPos.le
  rw [Real.rpow_zero, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hxpow), Real.norm_eq_abs,
    sub_zero, abs_of_nonneg hdeltaPos.le] at hmv
  refine le_of_mul_le_mul_right ?_ hdeltaPos
  simpa [div_eq_mul_inv, hdeltaPos.ne', mul_assoc, mul_comm] using hmv

end BombieriVinogradov.SiegelWalfisz
