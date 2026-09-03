import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedUnitSumNorm
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.RetainedCutoffLog
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The retained zero sum at one in the source error scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_truncatedCriticalZeroSum_one_le_sourceScale
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
              forall {x : Nat}, 2 < x ->
                forall {T : Real}, 2 <= T -> T <= x ->
                  norm (truncatedCriticalZeroSum chi 1 T exceptional) <=
                    C * ((x : Real) / T *
                      (Real.log ((N * x : Nat) : Real)) ^ 2)) := by
  choose C0 hC0Pos hReciprocal using
    exists_sum_norm_one_div_retainedCriticalZeroIndices_le hc
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive hRegularGap hRealUnique
    exceptional hChoice x hx T hT hTx
  have hTPos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  let L := Real.log ((N * x : Nat) : Real)
  have hReciprocalBound := hReciprocal hN hchi hPrimitive
    hRegularGap hRealUnique exceptional hChoice T hTPos
  have hUnit := (norm_truncatedCriticalZeroSum_one_le_sum_norm_one_div
    chi T exceptional).trans hReciprocalBound
  have hLogs :
      (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 <=
        4 * L ^ 2 := by
    exact log_level_add_log_ceil_add_two_sq_le_four_mul_sourceLog_sq
      hN hx hT hTx
  have hRatioRaw : T / T <= (x : Real) / T :=
    (div_le_div_iff_of_pos_right hTPos).2 hTx
  have hRatio : 1 <= (x : Real) / T := by
    simpa [ne_of_gt hTPos] using hRatioRaw
  have hGrowth : L ^ 2 <= (x : Real) / T * L ^ 2 := by
    calc
      L ^ 2 = 1 * L ^ 2 := by ring
      _ <= (x : Real) / T * L ^ 2 :=
        mul_le_mul_of_nonneg_right hRatio (sq_nonneg L)
  calc
    norm (truncatedCriticalZeroSum chi 1 T exceptional) <=
        C0 * (Real.log N +
          Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 := hUnit
    _ <= C0 * (4 * L ^ 2) :=
      mul_le_mul_of_nonneg_left hLogs (by positivity)
    _ = (4 * C0) * L ^ 2 := by ring
    _ <= (4 * C0) * ((x : Real) / T * L ^ 2) :=
      mul_le_mul_of_nonneg_left hGrowth (by positivity)
    _ = (4 * C0) * ((x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2) := by rfl

end BombieriVinogradov.SiegelWalfisz
