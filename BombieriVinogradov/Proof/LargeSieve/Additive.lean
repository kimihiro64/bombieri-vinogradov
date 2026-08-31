import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Rational spacing for the additive large sieve

Reduced rational points with denominators at most `Q` are separated by at
least `1 / Q^2`.  This is the arithmetic spacing input in Vaughan's additive
large-sieve theorem.
-/

set_option autoImplicit false

namespace BombieriVinogradov.LargeSieve

/-- A nonzero rational with denominator at most `D` has absolute value at least `1 / D`. -/
theorem ratAbsLowerBound {D : Nat} (hD : 0 < D) {z : Rat}
    (hzden : z.den <= D) (hz : Ne z 0) :
    (1 : Real) / (D : Real) <= |(z : Real)| := by
  have hnumNat : 1 <= z.num.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hz))
  have hnum : (1 : Real) <= |(z.num : Real)| := by
    calc
      (1 : Real) <= (z.num.natAbs : Real) := by exact_mod_cast hnumNat
      _ = |(z.num : Real)| := by simp
  have hDReal : 0 < (D : Real) := by exact_mod_cast hD
  have hdenReal : 0 < (z.den : Real) := by exact_mod_cast z.den_pos
  have hrecip : (1 : Real) / (D : Real) <= 1 / (z.den : Real) := by
    gcongr
  calc
    (1 : Real) / (D : Real) <= 1 / (z.den : Real) := hrecip
    _ <= |(z.num : Real)| / (z.den : Real) := by gcongr
    _ = |(z : Real)| := by
      rw [Rat.cast_def, abs_div, abs_of_pos hdenReal]

/-- Distinct rationals with denominators at most `Q` are at least `1 / Q^2` apart. -/
theorem ratAbsSubLowerBound {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx : x.den <= Q) (hy : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= |(x : Real) - (y : Real)| := by
  let z : Rat := x - y
  have hz : Ne z 0 := sub_ne_zero.mpr hxy
  have hden : z.den <= x.den * y.den :=
    Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
  have hdenQ : z.den <= Q ^ 2 := by
    calc
      z.den <= x.den * y.den := hden
      _ <= Q * Q := Nat.mul_le_mul hx hy
      _ = Q ^ 2 := by ring
  simpa [z, Nat.cast_pow] using
    ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hdenQ hz

/-- Circular distance between representatives in the half-open interval `[0, 1)`. -/
def ratCircleDistance (x y : Rat) : Real :=
  min |(x : Real) - (y : Real)| (1 - |(x : Real) - (y : Real)|)

/-- Farey-type rationals in `[0, 1)` remain `1 / Q^2` apart around the circle. -/
theorem ratCircleSeparation {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx0 : 0 <= x) (hx1 : x < 1) (hy0 : 0 <= y) (hy1 : y < 1)
    (hxden : x.den <= Q) (hyden : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance x y := by
  have hlinear := ratAbsSubLowerBound hQ hxden hyden hxy
  have hsub_lt_one : |x - y| < (1 : Rat) := by
    rw [abs_lt]
    constructor <;> linarith
  let w : Rat := 1 - |x - y|
  have hwpos : 0 < w := sub_pos.mpr hsub_lt_one
  have hwden : w.den <= Q ^ 2 := by
    have hxyden : (x - y).den <= Q ^ 2 := by
      apply Nat.le_trans
      · exact Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
      · simpa [pow_two] using Nat.mul_le_mul hxden hyden
    simpa [w] using hxyden
  have hcircular : (1 : Real) / (Q : Real) ^ 2 <= |(w : Real)| := by
    simpa only [Nat.cast_pow] using
      ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hwden hwpos.ne'
  have hwcast : |(w : Real)| = 1 - |(x : Real) - (y : Real)| := by
    rw [abs_of_pos]
    · simp [w]
    · exact_mod_cast hwpos
  rw [ratCircleDistance, le_min_iff]
  exact And.intro hlinear (hwcast ▸ hcircular)

end BombieriVinogradov.LargeSieve
