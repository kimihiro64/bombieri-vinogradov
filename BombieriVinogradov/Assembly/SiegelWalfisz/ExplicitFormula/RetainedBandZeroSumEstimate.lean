import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandZeroPointwiseBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite-sum estimate for the retained zero band

This module combines the band-zero pointwise estimate with an assumed
logarithmic cardinality bound and absorbs fixed logarithms quadratically.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_norm_one_div_retainedCriticalZeroBand_zero_le
    {c A : Real} (hc : 0 < c) (hA : 0 < A)
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hRegularGap : forall s : Complex,
      0 < s.re -> chi.LFunction s = 0 ->
        Or (Ne (chi ^ 2) 1) (Ne s.im 0) ->
          c / (Real.log N + Real.log (abs s.im + 2)) <= 1 - s.re)
    (hRealUnique : forall s t : Complex,
      0 < s.re -> 0 < t.re ->
        chi.LFunction s = 0 -> chi.LFunction t = 0 ->
          s.im = 0 -> t.im = 0 ->
            1 - s.re <= c / Real.log N ->
              1 - t.re <= c / Real.log N -> s = t)
    {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    (T : Real)
    (hCard : ((retainedCriticalZeroBand chi T exceptional 0).card : Real) <=
      A * (Real.log N + Real.log 2)) :
    Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
        (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
      (A / c) * (Real.log N + 2) ^ 2 := by
  let band := retainedCriticalZeroBand chi T exceptional 0
  let M := (Real.log N + Real.log 3) / c
  have hThreeReal : (3 : Real) <= (N : Real) :=
    (Nat.cast_le).2 hN
  have hOneReal : (1 : Real) <= (N : Real) :=
    by linarith
  have hLogNNonneg : 0 <= Real.log N :=
    Real.log_nonneg hOneReal
  have hLogThreeNonneg : 0 <= Real.log (3 : Real) :=
    Real.log_nonneg (by norm_num)
  have hMNonneg : 0 <= M := by
    dsimp [M]
    exact div_nonneg (add_nonneg hLogNNonneg hLogThreeNonneg)
      (le_of_lt hc)
  have hSumNsmul := Finset.sum_le_card_nsmul band
    (fun p => norm (1 / symmetricCompletedZeroValue p)) M
    (by
      intro p hp
      dsimp [M]
      have hpBand :
          (retainedCriticalZeroBand chi T exceptional 0 :
            Set (SymmetricCompletedZeroIndex chi)) p := hp
      exact norm_one_div_retainedCriticalZeroBand_zero_le (T := T)
        hc hN hchi hPrimitive hRegularGap hRealUnique hChoice
        hpBand)
  have hSum :
      Finset.sum band (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        (band.card : Real) * M := by
    simpa only [nsmul_eq_mul] using hSumNsmul
  have hLogTwoLeTwo : Real.log (2 : Real) <= 2 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (2 : Real) by norm_num)
    norm_num at h
    linarith
  have hLogThreeLeTwo : Real.log (3 : Real) <= 2 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (3 : Real) by norm_num)
    norm_num at h
    exact h
  have hFactorTwo :
      Real.log N + Real.log 2 <= Real.log N + 2 := by linarith
  have hFactorThree :
      Real.log N + Real.log 3 <= Real.log N + 2 := by linarith
  have hScaleNonneg : 0 <= Real.log N + 2 := by linarith
  have hCardLe : (band.card : Real) <= A * (Real.log N + 2) := by
    apply (show (band.card : Real) <=
      A * (Real.log N + Real.log 2) by simpa [band] using hCard).trans
    exact mul_le_mul_of_nonneg_left hFactorTwo (le_of_lt hA)
  have hMLe : M <= (Real.log N + 2) / c := by
    dsimp [M]
    exact div_le_div_of_nonneg_right hFactorThree (le_of_lt hc)
  calc
    Finset.sum band (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        (band.card : Real) * M := hSum
    _ <= (A * (Real.log N + 2)) * M :=
      mul_le_mul_of_nonneg_right hCardLe hMNonneg
    _ <= (A * (Real.log N + 2)) * ((Real.log N + 2) / c) :=
      mul_le_mul_of_nonneg_left hMLe
        (mul_nonneg (le_of_lt hA) hScaleNonneg)
    _ = (A / c) * (Real.log N + 2) ^ 2 := by ring

end BombieriVinogradov.SiegelWalfisz
