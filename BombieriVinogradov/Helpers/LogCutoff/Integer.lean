import BombieriVinogradov.Helpers.LogCutoff.Trapezoid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact Fourier cutoffs for integer products

For `Y >= 1`, the cutoff below is one at `log k` for positive integers
`k <= Y` and zero at `log k` for `k >= Y + 1`. Its Fourier representation
therefore separates the product constraint `m*n <= Y` multiplicatively.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped FourierTransform

namespace BombieriVinogradov.LogCutoff

/-- The logarithmic gap between consecutive positive integers. -/
def integerLogGap (Y : Nat) : Real :=
  Real.log ((Y + 1 : Nat) : Real) - Real.log (Y : Real)

/-- One quarter of the consecutive-integer logarithmic gap. -/
def integerLogEpsilon (Y : Nat) : Real :=
  integerLogGap Y / 4

/-- The trapezoidal log-space cutoff adapted to the integer endpoint `Y`. -/
def integerLogCutoff (Y : Nat) : Real -> Complex :=
  logTrapezoid (integerLogEpsilon Y) (Real.log (Y : Real))

theorem integerLogGap_pos (Y : Nat) (hY : 1 <= Y) : 0 < integerLogGap Y := by
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hsuccpos : 0 < ((Y + 1 : Nat) : Real) := by positivity
  have hlt : (Y : Real) < ((Y + 1 : Nat) : Real) := by exact_mod_cast Nat.lt_succ_self Y
  exact sub_pos.mpr (Real.strictMonoOn_log hYpos hsuccpos hlt)

theorem integerLogEpsilon_pos (Y : Nat) (hY : 1 <= Y) :
    0 < integerLogEpsilon Y := by
  exact div_pos (integerLogGap_pos Y hY) (by norm_num)

theorem log_nat_nonneg (Y : Nat) (hY : 1 <= Y) : 0 <= Real.log (Y : Real) := by
  exact Real.log_nonneg (by exact_mod_cast hY)

theorem integerLogCutoff_eq_one (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) (hkY : k <= Y) :
    integerLogCutoff Y (Real.log (k : Real)) = 1 := by
  have heps := integerLogEpsilon_pos Y hY
  have hkpos : 0 < (k : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hlogk : 0 <= Real.log (k : Real) := Real.log_nonneg (by exact_mod_cast hk)
  have hlogle : Real.log (k : Real) <= Real.log (Y : Real) :=
    Real.strictMonoOn_log.monotoneOn hkpos hYpos (by exact_mod_cast hkY)
  apply logTrapezoid_eq_one
  · exact heps
  · linarith
  · linarith

theorem integerLogCutoff_eq_zero (Y k : Nat) (hY : 1 <= Y)
    (hk : Y + 1 <= k) :
    integerLogCutoff Y (Real.log (k : Real)) = 0 := by
  have heps := integerLogEpsilon_pos Y hY
  have hsuccpos : 0 < ((Y + 1 : Nat) : Real) := by positivity
  have hkpos : 0 < (k : Real) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ Y) hk)
  have hlogle : Real.log ((Y + 1 : Nat) : Real) <= Real.log (k : Real) :=
    Real.strictMonoOn_log.monotoneOn hsuccpos hkpos (by exact_mod_cast hk)
  apply logTrapezoid_eq_zero_of_gt
  calc
    Real.log (Y : Real) + 2 * integerLogEpsilon Y <
        Real.log (Y : Real) + 4 * integerLogEpsilon Y := by linarith
    _ = Real.log ((Y + 1 : Nat) : Real) := by
      rw [integerLogEpsilon, integerLogGap]
      ring
    _ <= Real.log (k : Real) := hlogle

theorem continuousAt_integerLogCutoff (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    ContinuousAt (integerLogCutoff Y) (Real.log (k : Real)) := by
  have heps := integerLogEpsilon_pos Y hY
  have hkpos : 0 < (k : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hlogk : 0 <= Real.log (k : Real) := Real.log_nonneg (by exact_mod_cast hk)
  by_cases hkY : k <= Y
  · have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
    have hlogle : Real.log (k : Real) <= Real.log (Y : Real) :=
      Real.strictMonoOn_log.monotoneOn hkpos hYpos (by exact_mod_cast hkY)
    apply continuousAt_logTrapezoid_of_mem_plateau
    · exact heps
    · linarith
    · linarith
  · have hsucc : Y + 1 <= k := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hkY)
    have hsuccpos : 0 < ((Y + 1 : Nat) : Real) := by positivity
    have hlogle : Real.log ((Y + 1 : Nat) : Real) <= Real.log (k : Real) :=
      Real.strictMonoOn_log.monotoneOn hsuccpos hkpos (by exact_mod_cast hsucc)
    apply continuousAt_logTrapezoid_of_gt
    calc
      Real.log (Y : Real) + 2 * integerLogEpsilon Y <
          Real.log (Y : Real) + 4 * integerLogEpsilon Y := by linarith
      _ = Real.log ((Y + 1 : Nat) : Real) := by
        rw [integerLogEpsilon, integerLogGap]
        ring
      _ <= Real.log (k : Real) := hlogle

theorem integerLogCutoff_indicator (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    integerLogCutoff Y (Real.log (k : Real)) = if k <= Y then 1 else 0 := by
  split_ifs with hkY
  · exact integerLogCutoff_eq_one Y k hY hk hkY
  · exact integerLogCutoff_eq_zero Y k hY
      (Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hkY))

theorem integerLogCutoff_fourier_inversion (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    integerLogCutoff Y (Real.log (k : Real)) =
      ∫ xi : Real, Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi := by
  exact logTrapezoid_fourier_inversion
    (integerLogEpsilon Y) (Real.log (Y : Real)) (Real.log (k : Real))
    (integerLogEpsilon_pos Y hY) (log_nat_nonneg Y hY)
    (continuousAt_integerLogCutoff Y k hY hk)

theorem integerIndicator_fourier_representation (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    (if k <= Y then 1 else 0 : Complex) =
      ∫ xi : Real, Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi := by
  rw [← integerLogCutoff_fourier_inversion Y k hY hk]
  exact (integerLogCutoff_indicator Y k hY hk).symm

theorem fourier_integerLogCutoff_integrable (Y : Nat) (hY : 1 <= Y) :
    Integrable (𝓕 (integerLogCutoff Y)) := by
  exact fourier_logTrapezoid_integrable
    (integerLogEpsilon Y) (Real.log (Y : Real))
    (integerLogEpsilon_pos Y hY) (log_nat_nonneg Y hY)

theorem integral_norm_fourier_integerLogCutoff_le (Y : Nat) (hY : 1 <= Y) :
    ∫ xi : Real, ‖𝓕 (integerLogCutoff Y) xi‖ <=
      4 + 2 * Real.log ((Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
        integerLogEpsilon Y) := by
  exact integral_norm_fourier_logTrapezoid_le
    (integerLogEpsilon Y) (Real.log (Y : Real))
    (integerLogEpsilon_pos Y hY) (log_nat_nonneg Y hY)

theorem one_div_succ_le_integerLogGap (Y : Nat) (hY : 1 <= Y) :
    1 / ((Y : Real) + 1) <= integerLogGap Y := by
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hgap : integerLogGap Y = Real.log (1 + ((Y : Real))⁻¹) := by
    rw [integerLogGap, ← Real.log_div (by positivity) hYpos.ne']
    congr 1
    push_cast
    field_simp [hYpos.ne']
  rw [hgap]
  apply (show 1 / ((Y : Real) + 1) <=
    2 * ((Y : Real))⁻¹ / (((Y : Real))⁻¹ + 2) by
      field_simp [hYpos.ne']
      nlinarith).trans
  exact Real.le_log_one_add_of_nonneg (inv_nonneg.mpr hYpos.le)

theorem integerLogCutoff_ratio_le (Y : Nat) (hY : 1 <= Y) :
    (Real.log (Y : Real) + 3 * integerLogEpsilon Y) / integerLogEpsilon Y <=
      7 * ((Y : Real) + 1) ^ 2 := by
  let y : Real := Y
  let gap : Real := integerLogGap Y
  have hy : 1 <= y := by
    dsimp [y]
    exact_mod_cast hY
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hgap : 0 < gap := by exact integerLogGap_pos Y hY
  have hgapLower : 1 / (y + 1) <= gap := by
    simpa [y, gap] using one_div_succ_le_integerLogGap Y hY
  have hgapInv : gap⁻¹ <= y + 1 := by
    have h := (inv_le_inv₀ hgap (one_div_pos.mpr (by linarith))).2 hgapLower
    simpa [one_div] using h
  have hlogle : Real.log y <= y :=
    (Real.log_le_sub_one_of_pos hypos).trans (by linarith)
  have hproduct : Real.log y * gap⁻¹ <= y * (y + 1) := by
    exact mul_le_mul hlogle hgapInv (inv_nonneg.mpr hgap.le) hypos.le
  have hratio :
      (Real.log y + 3 * (gap / 4)) / (gap / 4) =
        4 * (Real.log y * gap⁻¹) + 3 := by
    field_simp [hgap.ne']
  change (Real.log y + 3 * (gap / 4)) / (gap / 4) <= 7 * (y + 1) ^ 2
  rw [hratio]
  nlinarith [sq_nonneg (y + 1)]

theorem log_integerLogCutoff_ratio_le (Y : Nat) (hY : 1 <= Y) :
    Real.log ((Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
      integerLogEpsilon Y) <= 6 + 2 * Real.log ((Y : Real) + 1) := by
  have heps := integerLogEpsilon_pos Y hY
  have hL := log_nat_nonneg Y hY
  have hratioPos : 0 <
      (Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
        integerLogEpsilon Y := div_pos (by linarith) heps
  have htargetPos : 0 < 7 * ((Y : Real) + 1) ^ 2 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hratioPos htargetPos
    (integerLogCutoff_ratio_le Y hY)
  have hlogSeven : Real.log (7 : Real) <= 6 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 7 by norm_num)
    norm_num at h ⊢
    exact h
  calc
    Real.log ((Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
        integerLogEpsilon Y) <= Real.log (7 * ((Y : Real) + 1) ^ 2) := hlog
    _ = Real.log 7 + 2 * Real.log ((Y : Real) + 1) := by
      rw [Real.log_mul (by norm_num : Ne (7 : Real) 0)
        (by positivity : Ne (((Y : Real) + 1) ^ 2) 0)]
      rw [Real.log_pow]
      norm_num
    _ <= 6 + 2 * Real.log ((Y : Real) + 1) := by linarith

theorem integral_norm_fourier_integerLogCutoff_le_log (Y : Nat) (hY : 1 <= Y) :
    ∫ xi : Real, ‖𝓕 (integerLogCutoff Y) xi‖ <=
      16 + 4 * Real.log ((Y : Real) + 1) := by
  exact (integral_norm_fourier_integerLogCutoff_le Y hY).trans
    (by linarith [log_integerLogCutoff_ratio_le Y hY])

end BombieriVinogradov.LogCutoff
