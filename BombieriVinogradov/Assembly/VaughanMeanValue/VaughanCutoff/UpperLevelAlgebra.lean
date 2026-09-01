import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.UpperLevelRatio
import Mathlib.Tactic

/-!
# Real inequalities for the upper inner Vaughan level

These lemmas bound all four cutoff terms from `Q^2 <= X <= Q^3` and a real
cutoff between `X/Q^2` and `X/Q^2 + 1`. Rounding and final composition remain
in separate modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem upperLevelXSqrtQ_le {x q : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hxCube : x <= q ^ 3) :
    x * Real.sqrt q <= x ^ (5 / 6 : Real) * q := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hsixth := upperLevelSixth_le_sqrt hx0 hq0 hxCube
  have hscaled := mul_le_mul_of_nonneg_right hsixth (Real.sqrt_nonneg q)
  have hroot : x ^ (1 / 6 : Real) * Real.sqrt q <= q := by
    nlinarith [Real.sq_sqrt hq0]
  have hfactor : x = x ^ (5 / 6 : Real) * x ^ (1 / 6 : Real) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  calc
    x * Real.sqrt q =
        (x ^ (5 / 6 : Real) * x ^ (1 / 6 : Real)) * Real.sqrt q :=
      congrArg (fun t : Real => t * Real.sqrt q) hfactor
    _ = x ^ (5 / 6 : Real) * (x ^ (1 / 6 : Real) * Real.sqrt q) := by ring
    _ <= x ^ (5 / 6 : Real) * q :=
      mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hx0 _)

theorem upperLevelRatioSqrtTerm_eq {x q : Real}
    (hx : 0 < x) (hq : Ne q 0) :
    upperLevelRatio x q * Real.sqrt x * q =
      x ^ (5 / 6 : Real) * (x ^ (2 / 3 : Real) / q) := by
  have hpowers :
      x ^ (5 / 6 : Real) * x ^ (2 / 3 : Real) = x * Real.sqrt x := by
    rw [← Real.rpow_add hx]
    rw [show (5 / 6 : Real) + 2 / 3 = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [upperLevelRatio]
  field_simp
  nlinarith

theorem upperLevelSmallTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqSqX : q ^ 2 <= x) (hxCube : x <= q ^ 3)
    (hu : u <= upperLevelRatio x q + 1) :
    u * q ^ 2 * Real.sqrt q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hq0 : 0 <= q := by linarith
  have hqne : Ne q 0 := by linarith
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hqX : q <= x := hqSq.trans hqSqX
  have hsqrt := Real.sqrt_le_sqrt hqX
  have huScaled := mul_le_mul_of_nonneg_right hu
    (show 0 <= q ^ 2 * Real.sqrt q by positivity)
  have hfirst := upperLevelXSqrtQ_le hx hq hxCube
  have hsecond := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg q)
  calc
    u * q ^ 2 * Real.sqrt q = u * (q ^ 2 * Real.sqrt q) := by ring
    _ <= (upperLevelRatio x q + 1) * (q ^ 2 * Real.sqrt q) := huScaled
    _ = upperLevelRatio x q * q ^ 2 * Real.sqrt q + q ^ 2 * Real.sqrt q := by ring
    _ = x * Real.sqrt q + q ^ 2 * Real.sqrt q := by
      rw [upperLevelRatio_mul_sq hqne]
    _ <= x ^ (5 / 6 : Real) * q + q ^ 2 * Real.sqrt x :=
      add_le_add hfirst hsecond
    _ = x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by ring

theorem upperLevelInverseTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hRatioU : upperLevelRatio x q <= u) :
    x * q / Real.sqrt u <= Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hqpos : 0 < q := by linarith
  have huPos : 0 < u := (upperLevelRatio_pos hxpos hqpos).trans_le hRatioU
  have hsqrtUPos : 0 < Real.sqrt u := Real.sqrt_pos.2 huPos
  have hden : Real.sqrt x / q <= Real.sqrt u := by
    rw [← sqrt_upperLevelRatio hx0 hq0]
    exact Real.sqrt_le_sqrt hRatioU
  have hproduct : x * q <= Real.sqrt x * q ^ 2 * Real.sqrt u := by
    calc
      x * q = Real.sqrt x * q ^ 2 * (Real.sqrt x / q) := by
        field_simp
        nlinarith [Real.sq_sqrt hx0]
      _ <= Real.sqrt x * q ^ 2 * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  exact (div_le_iff₀ hsqrtUPos).mpr hproduct

theorem upperLevelForwardTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hxCube : x <= q ^ 3)
    (hu : u <= upperLevelRatio x q + 1) :
    u * Real.sqrt x * q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hqpos : 0 < q := by linarith
  have htwoThird := upperLevelTwoThird_le_sq hx0 hq0 hxCube
  have hquotient : x ^ (2 / 3 : Real) / q <= q :=
    (div_le_iff₀ hqpos).mpr (by simpa [pow_two] using htwoThird)
  have hfirst := mul_le_mul_of_nonneg_left hquotient
    (Real.rpow_nonneg hx0 (5 / 6 : Real))
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hsecond := mul_le_mul_of_nonneg_left hqSq (Real.sqrt_nonneg x)
  have huScaled := mul_le_mul_of_nonneg_right hu
    (mul_nonneg (Real.sqrt_nonneg x) hq0)
  calc
    u * Real.sqrt x * q = u * (Real.sqrt x * q) := by ring
    _ <= (upperLevelRatio x q + 1) * (Real.sqrt x * q) := huScaled
    _ = upperLevelRatio x q * Real.sqrt x * q + Real.sqrt x * q := by ring
    _ = x ^ (5 / 6 : Real) * (x ^ (2 / 3 : Real) / q) +
        Real.sqrt x * q := by rw [upperLevelRatioSqrtTerm_eq hxpos (ne_of_gt hqpos)]
    _ <= x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 :=
      add_le_add hfirst hsecond

theorem upperLevelShortTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hu : u <= upperLevelRatio x q + 1) :
    u * q ^ 2 <= x + Real.sqrt x * q ^ 2 := by
  have hq0 : 0 <= q := by linarith
  have hqne : Ne q 0 := by linarith
  have hsqrtOne : 1 <= Real.sqrt x := by
    have hsqrt := Real.sqrt_le_sqrt hx
    simpa using hsqrt
  have hlast := mul_le_mul_of_nonneg_right hsqrtOne (sq_nonneg q)
  have huScaled := mul_le_mul_of_nonneg_right hu (sq_nonneg q)
  calc
    u * q ^ 2 <= (upperLevelRatio x q + 1) * q ^ 2 := huScaled
    _ = x + q ^ 2 := by rw [add_mul, upperLevelRatio_mul_sq hqne, one_mul]
    _ <= x + Real.sqrt x * q ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (by simpa using hlast) x

end BombieriVinogradov.VaughanMeanValue
