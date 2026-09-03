import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandCardBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandZeroSumEstimate
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Uniform reciprocal-norm bound for the retained zero band

This module supplies the uniform cardinality constant to the fixed-cardinality
low-band sum estimate.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_sum_norm_one_div_retainedCriticalZeroBand_zero_le
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
              forall T : Real,
                Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
                    (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
                  C * (Real.log N + 2) ^ 2) := by
  choose A hAPos hCard using exists_card_retainedCriticalZeroBand_le
  refine Exists.intro (A / c) (And.intro (div_pos hAPos hc) ?_)
  intro N inst hN chi hchi hPrimitive hRegularGap hRealUnique
    exceptional hChoice T
  apply sum_norm_one_div_retainedCriticalZeroBand_zero_le
    hc hAPos hN hchi hPrimitive hRegularGap hRealUnique hChoice T
  simpa using hCard hN hchi hPrimitive T exceptional 0

end BombieriVinogradov.SiegelWalfisz
