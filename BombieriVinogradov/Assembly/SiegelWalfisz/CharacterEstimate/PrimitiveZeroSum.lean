import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.WeightedZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring

/-!
# Uniform primitive retained-zero decay

The reciprocal-zero constant is chosen before every modulus, character,
argument, cutoff and faithful exceptional choice.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_truncatedCriticalZeroSum_le_exp_gap_mul_log_sq
    {c : Real} (hc : 0 < c) :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
          ExplicitFormulaZeroFreeData c chi ->
          forall (e : Option Complex), IsExceptionalZeroChoice c chi e ->
            forall {x : Nat}, 1 <= x -> forall {T : Real}, 0 < T ->
              norm (truncatedCriticalZeroSum chi x T e) <=
                K * ((x : Real) *
                  Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x)) *
                    (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2) := by
  choose K hKPos hK using exists_sum_norm_one_div_retainedCriticalZeroIndices_le hc
  refine Exists.intro K (And.intro hKPos ?_)
  intro N inst hN chi hchi hPrimitive hData e hChoice x hx T hT
  have hDecay := norm_truncatedCriticalZeroSum_le_exp_gap_mul_reciprocal_sum
    hc hN hchi hPrimitive hData e hChoice hx T
  have hReciprocal := hK hN hchi hPrimitive
    hData.regularGap hData.realUnique e hChoice T hT
  have hFactor : 0 <= (x : Real) *
      Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x) :=
    mul_nonneg (Nat.cast_nonneg x) (Real.exp_pos _).le
  have hBound := hDecay.trans (mul_le_mul_of_nonneg_left hReciprocal hFactor)
  calc
    norm (truncatedCriticalZeroSum chi x T e) <=
        ((x : Real) *
          Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x)) *
            (K * (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2) := hBound
    _ = K * ((x : Real) *
          Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x)) *
            (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 := by ring

end BombieriVinogradov.SiegelWalfisz
