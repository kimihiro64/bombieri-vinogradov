import BombieriVinogradov.Helpers.ComplexAnalysis.CpowLinearBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ReciprocalBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.NormNum

/-!
# The optional exceptional contribution at x=2

Uniform zero-free data place the exceptional zero to the right of three
quarters. Its endpoint contribution is therefore bounded by eight thirds.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_exceptionalZeroContribution_two_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N} {c : Real}
    (hData : ExplicitFormulaZeroFreeData c chi) (exceptional : Option Complex)
    (hChoice : IsExceptionalZeroChoice c chi exceptional) :
    norm (exceptionalZeroContribution 2 exceptional) <= (8 / 3 : Real) := by
  cases exceptional
  case none =>
    simp only [exceptionalZeroContribution, norm_zero]
    norm_num
  case some beta =>
    have hExceptional : IsExceptionalZero c chi beta := hChoice
    have hFacts := hData.exceptional beta hExceptional
    have hPower : norm ((2 : Complex) ^ beta / beta) <=
        2 * norm ((1 : Complex) / beta) := by
      simpa using
        BombieriVinogradov.ComplexAnalysis.norm_real_cpow_div_le_mul_norm_one_div
          (y := 2) (by norm_num) hExceptional.2.2.2.1.le
    have hReciprocal : norm ((1 : Complex) / beta) <= (4 / 3 : Real) :=
      norm_one_div_le_four_thirds_of_three_quarters_le_re hFacts.re_lower
    have hFinal : norm ((2 : Complex) ^ beta / beta) <= (8 / 3 : Real) := by
      calc
        norm ((2 : Complex) ^ beta / beta) <=
            2 * norm ((1 : Complex) / beta) := hPower
        _ <= 2 * (4 / 3 : Real) :=
          mul_le_mul_of_nonneg_left hReciprocal (by norm_num)
        _ = (8 / 3 : Real) := by norm_num
    simpa [exceptionalZeroContribution] using hFinal

end BombieriVinogradov.SiegelWalfisz
