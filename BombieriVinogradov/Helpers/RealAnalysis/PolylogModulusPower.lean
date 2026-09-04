import BombieriVinogradov.Helpers.RealAnalysis.SiegelExponentIdentities
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A modulus power bound at the Siegel exponent

Negative-power monotonicity and exact exponent cancellation convert
a polylogarithmic modulus range into the required two-thirds power.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem twoThirds_le_neg_siegelExponent_mul
    {A L N : Real} (hA : 0 < A) (hL : 0 < L) (hN : 0 < N)
    (hMod : N <= L ^ A) :
    L ^ (2 / 3 : Real) <= N ^ (-(1 / (3 * A))) * L := by
  have hExponentPos : 0 < 1 / (3 * A) := by positivity
  have hExponentNeg : -(1 / (3 * A)) <= 0 := by linarith
  have hPower := Real.rpow_le_rpow_of_nonpos hN hMod hExponentNeg
  rw [rpow_neg_siegelExponent_of_rpow hL hA] at hPower
  calc
    L ^ (2 / 3 : Real) = L ^ (-(1 / 3 : Real)) * L :=
      (rpow_neg_third_mul_self hL).symm
    _ <= N ^ (-(1 / (3 * A))) * L := mul_le_mul_of_nonneg_right hPower hL.le

end BombieriVinogradov.RealAnalysis
