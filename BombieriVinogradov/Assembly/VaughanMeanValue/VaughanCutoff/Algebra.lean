import Mathlib.Tactic

/-!
# Algebraic absorption for Vaughan cutoff estimates

Pure ordered-ring lemmas collect normalized logarithmic contributions into one
explicit constant. No analytic definitions are imported here.
-/

set_option autoImplicit false

namespace BombieriVinogradov.VaughanMeanValue

theorem scale_four_sq_le_eight_cube {S L : Real}
    (hS : 0 <= S) (hLtwo : L ^ 2 <= 2 * L ^ 3) :
    S * (4 * L ^ 2) <= S * (8 * L ^ 3) := by
  have hscaled := mul_le_mul_of_nonneg_left hLtwo hS
  nlinarith

theorem mul_le_two_sq {a b L : Real}
    (ha : 0 <= a) (hb : 0 <= b) (haL : a <= L) (hbL : b <= 2 * L) :
    a * b <= 2 * L ^ 2 := by
  have hmul := mul_le_mul haL hbL hb (by linarith : 0 <= L)
  nlinarith

theorem mul_le_sq {a b L : Real}
    (ha : 0 <= a) (hb : 0 <= b) (haL : a <= L) (hbL : b <= L) :
    a * b <= L ^ 2 := by
  have hmul := mul_le_mul haL hbL hb (by linarith : 0 <= L)
  nlinarith

theorem absorb_vaughan_terms
    {x a b c d short logX logXOne logTwoQ logu loguOne L S : Real}
    (hLhalf : 1 / 2 <= L)
    (hx : 0 <= x) (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hd : 0 <= d)
    (hlogX0 : 0 <= logX) (hlogXOne0 : 0 <= logXOne)
    (hlogTwoQ0 : 0 <= logTwoQ) (hlogu0 : 0 <= logu)
    (hloguOne0 : 0 <= loguOne) (hS : 0 <= S)
    (hxS : x <= S) (haS : a <= S) (hbS : b <= S) (hcS : c <= S)
    (hdS : d <= S) (hshortS : short <= S)
    (hlogX : logX <= L) (hlogXOne : logXOne <= 2 * L)
    (hlogTwoQ : logTwoQ <= L) (hlogu : logu <= L)
    (hloguOne : loguOne <= 2 * L) :
    (3 * x * logXOne ^ 2 + 4 * a * logTwoQ * logXOne) +
        (3 * x * logXOne ^ 2 + 2 * a * logu * logTwoQ +
          11520 * logX ^ 3 * (2 * x + 2 * b + 2 * c + 2 * d)) +
      11520 * logX ^ 3 * (2 * x + 3 * b + 2 * d) + short * loguOne <=
        200000 * S * L ^ 3 := by
  have hL : 0 <= L := by linarith
  have hLtwo : L ^ 2 <= 2 * L ^ 3 := by nlinarith [sq_nonneg L]
  have hLone : L <= 4 * L ^ 3 := by nlinarith [sq_nonneg L]
  have hlogXOneSq : logXOne ^ 2 <= 4 * L ^ 2 := by
    nlinarith [sq_nonneg (2 * L - logXOne)]
  have hbase : x * logXOne ^ 2 <= 8 * S * L ^ 3 := by
    calc
      _ <= S * (4 * L ^ 2) := mul_le_mul hxS hlogXOneSq (sq_nonneg _) hS
      _ <= S * (8 * L ^ 3) := scale_four_sq_le_eight_cube hS hLtwo
      _ = _ := by ring
  have hfirstLogs : a * logTwoQ * logXOne <= 4 * S * L ^ 3 := by
    have hlogs := mul_le_two_sq hlogTwoQ0 hlogXOne0 hlogTwoQ hlogXOne
    calc
      _ <= a * (2 * L ^ 2) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlogs ha
      _ <= S * (2 * L ^ 2) := mul_le_mul_of_nonneg_right haS (by positivity)
      _ <= 4 * S * L ^ 3 := by
        have := mul_le_mul_of_nonneg_left hLtwo hS
        nlinarith
  have hsecondLogs : a * logu * logTwoQ <= 2 * S * L ^ 3 := by
    have hlogs := mul_le_sq hlogu0 hlogTwoQ0 hlogu hlogTwoQ
    calc
      _ <= a * L ^ 2 := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlogs ha
      _ <= S * L ^ 2 := mul_le_mul_of_nonneg_right haS (sq_nonneg L)
      _ <= S * (2 * L ^ 3) := mul_le_mul_of_nonneg_left hLtwo hS
      _ = 2 * S * L ^ 3 := by ring
  have hlogXpow : logX ^ 3 <= L ^ 3 := by gcongr
  have hcoreTwo : 2 * x + 2 * b + 2 * c + 2 * d <= 8 * S := by linarith
  have hcoreThree : 2 * x + 3 * b + 2 * d <= 7 * S := by linarith
  have hlargeTwo : logX ^ 3 * (2 * x + 2 * b + 2 * c + 2 * d) <=
      8 * S * L ^ 3 := by
    nlinarith [mul_le_mul hlogXpow hcoreTwo (by positivity) (pow_nonneg hL 3)]
  have hlargeThree : logX ^ 3 * (2 * x + 3 * b + 2 * d) <=
      7 * S * L ^ 3 := by
    nlinarith [mul_le_mul hlogXpow hcoreThree (by positivity) (pow_nonneg hL 3)]
  have hremainder : short * loguOne <= 8 * S * L ^ 3 := by
    calc
      _ <= S * (2 * L) := mul_le_mul hshortS hloguOne hloguOne0 hS
      _ <= 8 * S * L ^ 3 := by
        have := mul_le_mul_of_nonneg_left hLone hS
        nlinarith
  nlinarith

end BombieriVinogradov.VaughanMeanValue
