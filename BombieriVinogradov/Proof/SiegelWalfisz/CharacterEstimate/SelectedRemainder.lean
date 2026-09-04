import BombieriVinogradov.Helpers.RealAnalysis.QuarterPowerDecay
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.PrimaryRemainderScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exponential decay of the complete explicit-formula remainder

The primary and secondary source terms retain their separate proofs.
Their exact coefficients sum to one uniform bound for the exported scale.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem explicitFormulaRemainderMajorant_selectedHeight_le_exp
    {a : Real} (ha : a <= (1 / 2 : Real)) {N x : Nat}
    (hN : 3 <= N) (hx : 3 <= x)
    (hModulus : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    explicitFormulaRemainderMajorant N x (Real.exp (Real.sqrt (Real.log x))) <=
      1568 * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hPrimary := primaryRemainder_selectedHeight_le_exp ha hN hx hModulus
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hSecondary := BombieriVinogradov.RealAnalysis.quarterPower_log_le_secondary_decay
    hxReal ha
  unfold explicitFormulaRemainderMajorant
  linarith

end BombieriVinogradov.SiegelWalfisz
