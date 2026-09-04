import BombieriVinogradov.Helpers.ComplexAnalysis.CpowDecayBound
import BombieriVinogradov.Helpers.RealAnalysis.LogModulusDecay
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ReciprocalBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ExceptionalGap
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Decay of an exceptional zero selected only at the primitive level

The ambient absence gives a logarithmic real-part gap. Its decay
and the reciprocal bound control the complete visible exceptional term.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_primitiveOnlyExceptionalContribution_le_exp
    {c a : Real} (hc : 0 < c) (hRate : a <= c / 4)
    {N x : Nat} [NeZero N] (hN : 3 <= N)
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1)
    (hData : ExplicitFormulaZeroFreeData c chi.primitiveCharacter)
    (hNone : IsExceptionalZeroChoice c chi none) {beta : Complex}
    (hExceptional : IsExceptionalZero c chi.primitiveCharacter beta)
    (hx : 3 <= x)
    (hMod : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    norm (exceptionalZeroContribution x (some beta)) <=
      (4 / 3 : Real) * ((x : Real) *
        Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hxOne : (1 : Real) <= (x : Real) := by linarith
  have hxNonneg : (0 : Real) <= (x : Real) := by linarith
  have hGap := primitiveExceptional_gap_of_ambient_none chi hchi hNone hExceptional
  have hRe : beta.re <= 1 - c / Real.log N := by linarith
  have hReciprocal := norm_one_div_le_four_thirds_of_three_quarters_le_re
    (hData.exceptional beta hExceptional).re_lower
  have hPower : norm (exceptionalZeroContribution x (some beta)) <=
      ((x : Real) * Real.exp (-(c / Real.log N) * Real.log x)) *
        norm ((1 : Complex) / beta) := by
    have h := BombieriVinogradov.ComplexAnalysis.norm_real_cpow_div_le_exp_gap_mul_reciprocal
      hxOne hRe
    simpa only [exceptionalZeroContribution, Complex.ofReal_natCast] using h
  have hDecay := BombieriVinogradov.RealAnalysis.exp_neg_logModulus_gap_le_exp
    hc hRate hN hx hMod
  calc
    norm (exceptionalZeroContribution x (some beta)) <=
        ((x : Real) * Real.exp (-(c / Real.log N) * Real.log x)) *
          norm ((1 : Complex) / beta) := hPower
    _ <= ((x : Real) * Real.exp (-(c / Real.log N) * Real.log x)) * (4 / 3) :=
      mul_le_mul_of_nonneg_left hReciprocal (by positivity)
    _ <= ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) * (4 / 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDecay hxNonneg) (by norm_num)
    _ = (4 / 3 : Real) * ((x : Real) *
        Real.exp (-(a * Real.sqrt (Real.log x)))) := by ring

end BombieriVinogradov.SiegelWalfisz
