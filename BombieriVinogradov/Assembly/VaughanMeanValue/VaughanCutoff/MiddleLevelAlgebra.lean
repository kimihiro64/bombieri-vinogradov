import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.MiddleLevelPowers
import Mathlib.Tactic

/-!
# Real inequalities for the middle Vaughan level

The four analytic cutoff terms are bounded using `Q^3 <= X` and a real cutoff
between `X^(1/3)` and `X^(1/3) + 1`. Integer rounding and final composition are
owned by separate modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem middleLevelQSqrt_le_sqrtX {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hqCubeX : q ^ 3 <= x) :
    q * Real.sqrt q <= Real.sqrt x := by
  apply (pow_le_pow_iff_left₀ (mul_nonneg hq (Real.sqrt_nonneg q))
    (Real.sqrt_nonneg x) (by norm_num : Ne (2 : Nat) 0)).mp
  rw [mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hx]
  nlinarith

theorem middleLevelSqrtQ_le_sqrtX {x q : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqCubeX : q ^ 3 <= x) :
    Real.sqrt q <= Real.sqrt x := by
  apply Real.sqrt_le_sqrt
  have hqRoot := le_middleLevelRoot_of_cube_le (by positivity) (by linarith) hqCubeX
  exact hqRoot.trans (middleLevelRoot_le_self hx)

theorem middleLevelSmallTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqCubeX : q ^ 3 <= x)
    (hu : u <= middleLevelRoot x + 1) :
    u * q ^ 2 * Real.sqrt q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hroot0 : 0 <= middleLevelRoot x := middleLevelRoot_nonneg hx0
  have hqSqrt := middleLevelQSqrt_le_sqrtX hx0 hq0 hqCubeX
  have hsqrt := middleLevelSqrtQ_le_sqrtX hx hq hqCubeX
  have huScaled := mul_le_mul_of_nonneg_right hu
    (show 0 <= q ^ 2 * Real.sqrt q by positivity)
  have hfirst := mul_le_mul_of_nonneg_left hqSqrt
    (mul_nonneg hroot0 hq0)
  have hsecond := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg q)
  calc
    u * q ^ 2 * Real.sqrt q = u * (q ^ 2 * Real.sqrt q) := by ring
    _ <= (middleLevelRoot x + 1) * (q ^ 2 * Real.sqrt q) := huScaled
    _ = middleLevelRoot x * q * (q * Real.sqrt q) + q ^ 2 * Real.sqrt q := by ring
    _ <= middleLevelRoot x * q * Real.sqrt x + q ^ 2 * Real.sqrt x :=
      add_le_add hfirst hsecond
    _ = x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
      rw [show middleLevelRoot x * q * Real.sqrt x =
        (middleLevelRoot x * Real.sqrt x) * q by ring,
        middleLevelRoot_mul_sqrt hxpos]
      ring

theorem middleLevelInverseTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hrootU : middleLevelRoot x <= u) :
    x * q / Real.sqrt u <= x ^ (5 / 6 : Real) * q := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have huPos : 0 < u := (middleLevelRoot_pos hxpos).trans_le hrootU
  have hsqrtUPos : 0 < Real.sqrt u := Real.sqrt_pos.2 huPos
  have hden : x ^ (1 / 6 : Real) <= Real.sqrt u := by
    rw [← sqrt_middleLevelRoot hx0]
    exact Real.sqrt_le_sqrt hrootU
  have hproduct : x <= x ^ (5 / 6 : Real) * Real.sqrt u := by
    calc
      x = x ^ (5 / 6 : Real) * x ^ (1 / 6 : Real) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      _ <= x ^ (5 / 6 : Real) * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hx0 _)
  have hquotient : x / Real.sqrt u <= x ^ (5 / 6 : Real) :=
    (div_le_iff₀ hsqrtUPos).mpr hproduct
  calc
    x * q / Real.sqrt u = (x / Real.sqrt u) * q := by ring
    _ <= x ^ (5 / 6 : Real) * q :=
      mul_le_mul_of_nonneg_right hquotient hq0

theorem middleLevelForwardTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hu : u <= middleLevelRoot x + 1) :
    u * Real.sqrt x * q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have huScaled := mul_le_mul_of_nonneg_right hu
    (mul_nonneg (Real.sqrt_nonneg x) hq0)
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hsqrtScaled := mul_le_mul_of_nonneg_left hqSq (Real.sqrt_nonneg x)
  calc
    u * Real.sqrt x * q = u * (Real.sqrt x * q) := by ring
    _ <= (middleLevelRoot x + 1) * (Real.sqrt x * q) := huScaled
    _ = (middleLevelRoot x * Real.sqrt x) * q + Real.sqrt x * q := by ring
    _ <= (middleLevelRoot x * Real.sqrt x) * q + Real.sqrt x * q ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hsqrtScaled (middleLevelRoot x * Real.sqrt x * q)
    _ = x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
      rw [middleLevelRoot_mul_sqrt hxpos]

theorem middleLevelShortTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqCubeX : q ^ 3 <= x)
    (hu : u <= middleLevelRoot x + 1) :
    u * q ^ 2 <= x + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hq0 : 0 <= q := by linarith
  have hroot0 : 0 <= middleLevelRoot x := middleLevelRoot_nonneg hx0
  have hqRoot := le_middleLevelRoot_of_cube_le hx0 hq0 hqCubeX
  have hqSq := pow_le_pow_left₀ hq0 hqRoot 2
  have hrootScaled := mul_le_mul_of_nonneg_left hqSq hroot0
  have hrootTerm : middleLevelRoot x * q ^ 2 <= x := by
    calc
      middleLevelRoot x * q ^ 2 <=
          middleLevelRoot x * middleLevelRoot x ^ 2 := hrootScaled
      _ = middleLevelRoot x ^ 3 := by ring
      _ = x := middleLevelRoot_cube hx0
  have hsqrtOne : 1 <= Real.sqrt x := by
    have hsqrt := Real.sqrt_le_sqrt hx
    simpa using hsqrt
  have hlast := mul_le_mul_of_nonneg_right hsqrtOne (sq_nonneg q)
  have huScaled := mul_le_mul_of_nonneg_right hu (sq_nonneg q)
  calc
    u * q ^ 2 <= (middleLevelRoot x + 1) * q ^ 2 := huScaled
    _ = middleLevelRoot x * q ^ 2 + q ^ 2 := by ring
    _ <= x + Real.sqrt x * q ^ 2 := add_le_add hrootTerm (by simpa using hlast)

end BombieriVinogradov.VaughanMeanValue
