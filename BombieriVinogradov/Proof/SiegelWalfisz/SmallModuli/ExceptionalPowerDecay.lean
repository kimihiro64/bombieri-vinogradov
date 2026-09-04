import BombieriVinogradov.Helpers.ComplexAnalysis.CpowDecayBound
import BombieriVinogradov.Helpers.RealAnalysis.PolylogarithmicExponentialDecay
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ReciprocalBound
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exceptional power decay in the polylogarithmic range

The Siegel-sized real-part gap and reciprocal estimate control the
visible exceptional contribution down to the natural endpoint two.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_exceptionalPower_le_polylog_decay
    {a A k : Real} (ha : 0 <= a) (hA : 0 < A) (hk : 0 < k)
    {N x : Nat} (hN : (0 : Real) < (N : Real)) (hx : 2 <= x)
    (hMod : (N : Real) <= (Real.log x) ^ A) {beta : Complex}
    (hLower : (3 / 4 : Real) <= beta.re)
    (hGap : k * (N : Real) ^ (-(1 / (3 * A))) <= 1 - beta.re) :
    norm (exceptionalZeroContribution x (some beta)) <=
      ((4 / 3 : Real) * Real.exp (a ^ 4 / k ^ 3)) *
        ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hxReal : (2 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hxOne : (1 : Real) <= (x : Real) := by linarith
  have hxNonneg : (0 : Real) <= (x : Real) := by linarith
  have hLog : 0 < Real.log x := Real.log_pos (by linarith)
  have hRe : beta.re <= 1 - k * (N : Real) ^ (-(1 / (3 * A))) := by linarith
  have hReciprocal := norm_one_div_le_four_thirds_of_three_quarters_le_re hLower
  have hPower : norm (exceptionalZeroContribution x (some beta)) <=
      ((x : Real) * Real.exp (-(k * (N : Real) ^ (-(1 / (3 * A)))) * Real.log x)) *
        norm ((1 : Complex) / beta) := by
    have h := BombieriVinogradov.ComplexAnalysis.norm_real_cpow_div_le_exp_gap_mul_reciprocal
      hxOne hRe
    simpa only [exceptionalZeroContribution, Complex.ofReal_natCast] using h
  have hDecay := BombieriVinogradov.RealAnalysis.exp_neg_siegelPower_mul_le_exp_sqrt
    ha hA hk hLog hN hMod
  calc
    norm (exceptionalZeroContribution x (some beta)) <=
        ((x : Real) * Real.exp (-(k * (N : Real) ^ (-(1 / (3 * A)))) * Real.log x)) *
          norm ((1 : Complex) / beta) := hPower
    _ <= ((x : Real) * Real.exp (-(k * (N : Real) ^ (-(1 / (3 * A)))) * Real.log x)) *
        (4 / 3) := mul_le_mul_of_nonneg_left hReciprocal (by positivity)
    _ <= ((x : Real) * (Real.exp (a ^ 4 / k ^ 3) *
        Real.exp (-(a * Real.sqrt (Real.log x))))) * (4 / 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDecay hxNonneg) (by norm_num)
    _ = ((4 / 3 : Real) * Real.exp (a ^ 4 / k ^ 3)) *
        ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by ring

end BombieriVinogradov.SiegelWalfisz
