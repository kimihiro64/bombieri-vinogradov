import BombieriVinogradov.Helpers.RealAnalysis.FractionalExponentialDecay
import BombieriVinogradov.Helpers.RealAnalysis.PolylogModulusPower
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exponential decay from a polylogarithmic modulus bound

The Siegel modulus power bound and fractional damping preserve the
target square-root rate at an explicit coefficient cost.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem exp_neg_siegelPower_mul_le_exp_sqrt
    {a A k L N : Real} (ha : 0 <= a) (hA : 0 < A) (hk : 0 < k)
    (hL : 0 < L) (hN : 0 < N) (hMod : N <= L ^ A) :
    Real.exp (-(k * N ^ (-(1 / (3 * A)))) * L) <=
      Real.exp (a ^ 4 / k ^ 3) * Real.exp (-(a * Real.sqrt L)) := by
  have hPower := twoThirds_le_neg_siegelExponent_mul hA hL hN hMod
  have hScaled := mul_le_mul_of_nonneg_left hPower hk.le
  have hExponent : -(k * N ^ (-(1 / (3 * A)))) * L <=
      -(k * L ^ (2 / 3 : Real)) := by
    calc
      -(k * N ^ (-(1 / (3 * A)))) * L =
          -(k * (N ^ (-(1 / (3 * A))) * L)) := by ring
      _ <= -(k * L ^ (2 / 3 : Real)) := neg_le_neg hScaled
  exact (Real.exp_le_exp.mpr hExponent).trans
    (exp_neg_twoThirds_le_exp_sqrt ha hk hL.le)

end BombieriVinogradov.RealAnalysis
