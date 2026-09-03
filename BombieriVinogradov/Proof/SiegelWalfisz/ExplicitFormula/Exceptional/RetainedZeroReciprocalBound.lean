import BombieriVinogradov.Helpers.ComplexAnalysis.ReciprocalRealGap
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.RetainedZeroLeftGap
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pointwise retained-zero reciprocal bound
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_one_div_retainedCriticalZero_le
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
    (hp : (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    norm (1 / symmetricCompletedZeroValue p) <=
      (Real.log N +
        Real.log (abs (symmetricCompletedZeroValue p).im + 2)) / c := by
  let L : Real := Real.log N +
    Real.log (abs (symmetricCompletedZeroValue p).im + 2)
  have hThreeReal : (3 : Real) <= (N : Real) :=
    (Nat.cast_le).2 hN
  have hLogThreePos : 0 < Real.log (3 : Real) :=
    Real.log_pos (by norm_num)
  have hLogNLower : Real.log (3 : Real) <= Real.log N :=
    Real.log_le_log (by norm_num) hThreeReal
  have hLogNPos : 0 < Real.log N :=
    hLogThreePos.trans_le hLogNLower
  have hLogHeightNonneg :
      0 <= Real.log (abs (symmetricCompletedZeroValue p).im + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg (symmetricCompletedZeroValue p).im]
  have hLPos : 0 < L := by
    dsimp [L]
    linarith
  have hGap := retainedCriticalZero_re_gap
    hc hN hchi hPrimitive hRegularGap hRealUnique hChoice hp
  have hBound :
      norm (1 / symmetricCompletedZeroValue p) <= L / c :=
    BombieriVinogradov.ComplexAnalysis.norm_one_div_le_scale_div_of_re_gap
      hc hLPos
        (by simpa [L] using hGap)
  simpa [L] using hBound

end BombieriVinogradov.SiegelWalfisz
