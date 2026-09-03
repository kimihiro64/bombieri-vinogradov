import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandSumEstimate
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandZeroSumBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedPositiveBandSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Positivity

/-!
# Uniform bound for the complete retained reciprocal-zero cutoff
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_sum_norm_one_div_retainedCriticalZeroIndices_le
    {c : Real} (hc : 0 < c) :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
          (forall s : Complex,
            0 < s.re -> chi.LFunction s = 0 ->
              Or (Ne (chi ^ 2) 1) (Ne s.im 0) ->
                c / (Real.log N + Real.log (abs s.im + 2)) <=
                  1 - s.re) ->
          (forall s t : Complex,
            0 < s.re -> 0 < t.re ->
              chi.LFunction s = 0 -> chi.LFunction t = 0 ->
                s.im = 0 -> t.im = 0 ->
                  1 - s.re <= c / Real.log N ->
                    1 - t.re <= c / Real.log N -> s = t) ->
          forall (exceptional : Option Complex),
            IsExceptionalZeroChoice c chi exceptional ->
              forall T : Real, 0 < T ->
                Finset.sum (retainedCriticalZeroIndices chi T exceptional)
                    (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
                  C *
                    (Real.log N +
                      Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2) := by
  choose C0 hC0Pos hLow using
    exists_sum_norm_one_div_retainedCriticalZeroBand_zero_le hc
  choose C1 hC1Pos hPositive using
    exists_sum_norm_one_div_retainedCriticalZeroBand_le
  refine Exists.intro (4 * C0 + C1) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive hRegularGap hRealUnique
    exceptional hChoice T hT
  apply sum_norm_one_div_retainedCriticalZeroIndices_le
    hT exceptional (le_of_lt hC0Pos) (le_of_lt hC1Pos) hN
  exact hLow hN hchi hPrimitive hRegularGap hRealUnique
    exceptional hChoice T
  intro k hk
  exact hPositive hN hchi hPrimitive T exceptional k hk

end BombieriVinogradov.SiegelWalfisz
