import Mathlib.Tactic

/-!
# Algebraic bounds for the outer Vaughan range

Pure real inequalities bound the specialized maximal-bilinear square roots and
absorb their two logarithmic factors into the common cubic logarithmic scale.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem outerRangeSqrtProduct_le {x q ell : Real}
    (hx : 0 <= x) (hq : 1 <= q) (hxq : x <= q ^ 2) (hell : 0 <= ell) :
    Real.sqrt (36 * (1 + q ^ 2)) *
        Real.sqrt (36 * (x + q ^ 2) * (x * ell ^ 2)) <=
      81 * Real.sqrt x * q ^ 2 * ell := by
  have hq0 : 0 <= q := by linarith
  have honeq : 1 <= q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hfirst : Real.sqrt (36 * (1 + q ^ 2)) <= 9 * q := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hxplus : x + q ^ 2 <= 2 * q ^ 2 := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hxplus
    (mul_nonneg hx (sq_nonneg ell))
  have hsecondRad :
      36 * (x + q ^ 2) * (x * ell ^ 2) <=
        (9 * q * Real.sqrt x * ell) ^ 2 := by
    rw [show (9 * q * Real.sqrt x * ell) ^ 2 =
      81 * q ^ 2 * x * ell ^ 2 by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hx]
        ring]
    have hterm : 0 <= q ^ 2 * (x * ell ^ 2) := by positivity
    calc
      _ = 36 * ((x + q ^ 2) * (x * ell ^ 2)) := by ring
      _ <= 36 * (2 * q ^ 2 * (x * ell ^ 2)) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ <= 81 * q ^ 2 * x * ell ^ 2 := by nlinarith
  have hsecond : Real.sqrt (36 * (x + q ^ 2) * (x * ell ^ 2)) <=
      9 * q * Real.sqrt x * ell := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, hsecondRad⟩
  calc
    _ <= (9 * q) * (9 * q * Real.sqrt x * ell) :=
      mul_le_mul hfirst hsecond (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

theorem outerRangeLogProduct_le
    {sqrtTerm ell ellOne L S : Real}
    (hLhalf : 1 / 2 <= L) (hsqrt : 0 <= sqrtTerm)
    (hell : 0 <= ell) (hellOne : 0 <= ellOne) (hS : 0 <= S)
    (hsqrtS : sqrtTerm <= S) (hellL : ell <= L)
    (hellOneL : ellOne <= 2 * L) :
    (16 + 4 * ellOne) * (81 * sqrtTerm * ell) <=
      6480 * S * L ^ 3 := by
  have hL : 0 <= L := by linarith
  have hfactor0 : 0 <= 16 + 4 * ellOne := by linarith
  have hfactor : 16 + 4 * ellOne <= 40 * L := by linarith [hfactor0]
  have hproduct : sqrtTerm * ell <= S * L :=
    mul_le_mul hsqrtS hellL hell hS
  have hcore : 81 * sqrtTerm * ell <= 81 * S * L := by nlinarith
  have hcore0 : 0 <= 81 * sqrtTerm * ell := by positivity
  have hupper0 : 0 <= 40 * L := by positivity
  have hLsq : L ^ 2 <= 2 * L ^ 3 := by nlinarith [sq_nonneg L]
  calc
    _ <= (40 * L) * (81 * S * L) := by
      exact mul_le_mul hfactor hcore hcore0 hupper0
    _ = 3240 * S * L ^ 2 := by ring
    _ <= 6480 * S * L ^ 3 := by
      have hscaled := mul_le_mul_of_nonneg_left hLsq (by positivity : 0 <= 3240 * S)
      nlinarith

end BombieriVinogradov.VaughanMeanValue
