import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.RetainedZeroReciprocalBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pointwise reciprocal bound in the retained zero band

This module replaces the variable height logarithm by log 3 for zeros whose
absolute ordinates lie below one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_one_div_retainedCriticalZeroBand_zero_le
    {c : Real} (hc : 0 < c)
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hRegularGap : forall s : Complex,
      0 < s.re -> chi.LFunction s = 0 ->
        Or (Ne (chi ^ 2) 1) (Ne s.im 0) ->
          c / (Real.log N + Real.log (abs s.im + 2)) <=
            1 - s.re)
    (hRealUnique : forall s t : Complex,
      0 < s.re -> 0 < t.re ->
        chi.LFunction s = 0 -> chi.LFunction t = 0 ->
          s.im = 0 -> t.im = 0 ->
            1 - s.re <= c / Real.log N ->
              1 - t.re <= c / Real.log N -> s = t)
    {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    {T : Real} {p : SymmetricCompletedZeroIndex chi}
    (hp : (retainedCriticalZeroBand chi T exceptional 0 :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    norm (1 / symmetricCompletedZeroValue p) <=
      (Real.log N + Real.log 3) / c := by
  have hBand := (mem_retainedCriticalZeroBand_iff).mp hp
  have hBase :
      norm (1 / symmetricCompletedZeroValue p) <=
        (Real.log N +
          Real.log (abs (symmetricCompletedZeroValue p).im + 2)) / c :=
    norm_one_div_retainedCriticalZero_le hc hN hchi hPrimitive
      hRegularGap hRealUnique hChoice hBand.1
  have hAbsLtOne :
      abs (symmetricCompletedZeroValue p).im < 1 := by
    simpa using hBand.2.2
  have hArgPos :
      0 < abs (symmetricCompletedZeroValue p).im + 2 := by
    linarith [abs_nonneg (symmetricCompletedZeroValue p).im]
  have hArgLeThree :
      abs (symmetricCompletedZeroValue p).im + 2 <= 3 := by
    linarith
  have hLogHeight :
      Real.log (abs (symmetricCompletedZeroValue p).im + 2) <=
        Real.log 3 :=
    Real.log_le_log hArgPos hArgLeThree
  have hNumerator :
      Real.log N +
          Real.log (abs (symmetricCompletedZeroValue p).im + 2) <=
        Real.log N + Real.log 3 := by
    simpa [add_comm] using add_le_add_left hLogHeight (Real.log N)
  exact hBase.trans
    (div_le_div_of_nonneg_right hNumerator (le_of_lt hc))

end BombieriVinogradov.SiegelWalfisz
