import Mathlib.Tactic

/-!
# Cube-root identities for the middle Vaughan level

This module owns only the real cube-root notation and exact power identities
used by the middle cutoff. Integer rounding and analytic inequalities remain
in separate outward modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

def middleLevelRoot (x : Real) : Real := x ^ (1 / 3 : Real)

theorem middleLevelRoot_nonneg {x : Real} (hx : 0 <= x) :
    0 <= middleLevelRoot x := by
  exact Real.rpow_nonneg hx _

theorem middleLevelRoot_pos {x : Real} (hx : 0 < x) :
    0 < middleLevelRoot x := by
  exact Real.rpow_pos_of_pos hx _

theorem middleLevelRoot_cube {x : Real} (hx : 0 <= x) :
    middleLevelRoot x ^ 3 = x := by
  simpa [middleLevelRoot, one_div] using
    (Real.rpow_inv_natCast_pow hx (by norm_num : Ne (3 : Nat) 0))

theorem middleLevelRoot_mul_sqrt {x : Real} (hx : 0 < x) :
    middleLevelRoot x * Real.sqrt x = x ^ (5 / 6 : Real) := by
  rw [middleLevelRoot, Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  norm_num

theorem sqrt_middleLevelRoot {x : Real} (hx : 0 <= x) :
    Real.sqrt (middleLevelRoot x) = x ^ (1 / 6 : Real) := by
  rw [Real.sqrt_eq_rpow, middleLevelRoot, ← Real.rpow_mul hx]
  norm_num

theorem middleLevelRoot_le_self {x : Real} (hx : 1 <= x) :
    middleLevelRoot x <= x := by
  have hpow := Real.rpow_le_rpow_of_exponent_le hx
    (by norm_num : (1 / 3 : Real) <= 1)
  simpa [middleLevelRoot] using hpow

theorem le_middleLevelRoot_of_cube_le {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hqCubeX : q ^ 3 <= x) :
    q <= middleLevelRoot x := by
  apply (pow_le_pow_iff_left₀ hq (middleLevelRoot_nonneg hx)
    (by norm_num : Ne (3 : Nat) 0)).mp
  rw [middleLevelRoot_cube hx]
  exact hqCubeX

end BombieriVinogradov.VaughanMeanValue
