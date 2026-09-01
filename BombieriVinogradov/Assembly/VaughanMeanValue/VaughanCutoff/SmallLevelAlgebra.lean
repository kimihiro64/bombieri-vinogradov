import Mathlib.Tactic

/-!
# Real algebra for the small Vaughan level

These lemmas derive the four real cutoff inequalities from `1 <= q` and
`q^6 <= x`. Natural cutoff construction and final analytic composition are
owned by separate modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem smallLevelSqrt_le_sq {q : Real} (hq : 1 <= q) :
    Real.sqrt q <= q ^ 2 := by
  have hq0 : 0 <= q := by linarith
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hqSqOne : 1 <= q ^ 2 := hq.trans hqSq
  have hqFourth : q ^ 2 <= (q ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hqSqOne)]
  apply Real.sqrt_le_iff.mpr
  exact And.intro (sq_nonneg q) (hqSq.trans hqFourth)

theorem smallLevelSmallTerm_le {x q : Real}
    (hq : 1 <= q) (hqSixthX : q ^ 6 <= x) :
    q ^ 2 * q ^ 2 * Real.sqrt q <= x := by
  have hscaled := mul_le_mul_of_nonneg_left (smallLevelSqrt_le_sq hq)
    (show 0 <= q ^ 2 * q ^ 2 by positivity)
  calc
    q ^ 2 * q ^ 2 * Real.sqrt q <= q ^ 2 * q ^ 2 * q ^ 2 := hscaled
    _ = q ^ 6 := by ring
    _ <= x := hqSixthX

theorem smallLevelInverseTerm_eq {x q : Real} (hq : 1 <= q) :
    x * q / Real.sqrt (q ^ 2) = x := by
  have hq0 : 0 <= q := by linarith
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hq0]
  field_simp [show Ne q 0 by linarith]

theorem smallLevelForwardTerm_le {x q : Real}
    (hx : 0 <= x) (hq : 1 <= q) (hqSixthX : q ^ 6 <= x) :
    q ^ 2 * Real.sqrt x * q <= x := by
  have hq0 : 0 <= q := by linarith
  have hcube0 : 0 <= q ^ 3 := by positivity
  have hcube : q ^ 3 <= Real.sqrt x := by
    have hsqrt := Real.sqrt_le_sqrt hqSixthX
    rw [show q ^ 6 = (q ^ 3) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hcube0] at hsqrt
    exact hsqrt
  have hscaled := mul_le_mul_of_nonneg_right hcube (Real.sqrt_nonneg x)
  calc
    q ^ 2 * Real.sqrt x * q = q ^ 3 * Real.sqrt x := by ring
    _ <= Real.sqrt x * Real.sqrt x := hscaled
    _ = x := by nlinarith [Real.sq_sqrt hx]

theorem smallLevelShortTerm_le {x q : Real}
    (hq : 1 <= q) (hqSixthX : q ^ 6 <= x) :
    q ^ 2 * q ^ 2 <= x := by
  have hq0 : 0 <= q := by linarith
  have hqSqOne : 1 <= q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hscaled := mul_le_mul_of_nonneg_left hqSqOne
    (show 0 <= q ^ 4 by positivity)
  calc
    q ^ 2 * q ^ 2 = q ^ 4 := by ring
    _ <= q ^ 4 * q ^ 2 := by simpa using hscaled
    _ = q ^ 6 := by ring
    _ <= x := hqSixthX

end BombieriVinogradov.VaughanMeanValue
