import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Near-zero reference reciprocal bound

This module bounds the reference-point reciprocal terms for completed
zeros in the open unit height window. It uses only critical-strip geometry
and the existing multiplicity-counted window-cardinality estimate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_tsum_norm_reference_reciprocal_near_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real,
              (tsum fun p : SymmetricCompletedZeroIndex chi =>
                if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
                  norm (1 / (((2 : Real) : Complex) +
                    (T : Complex) * Complex.I -
                      symmetricCompletedZeroValue p))
                else 0) <=
                  C * (Real.log N + Real.log (abs T + 2))) := by
  choose C hCPos hCount using exists_ncard_zeroHeightWindow_le
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T
  have hWindowData := hCount hN hchi hPrimitive T
  have hFinite := hWindowData.1
  have hCardBound := hWindowData.2
  let nearTerm : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
      norm (1 / (((2 : Real) : Complex) +
        (T : Complex) * Complex.I - symmetricCompletedZeroValue p))
    else 0
  change tsum nearTerm <=
    C * (Real.log N + Real.log (abs T + 2))
  rw [tsum_eq_sum (fun p hpOutside => by
    dsimp [nearTerm]
    rw [if_neg]
    intro hpNear
    apply hpOutside
    apply (hFinite.mem_toFinset).mpr
    change abs (T - (symmetricCompletedZeroValue p).im) < 1
    exact hpNear)]
  calc
    Finset.sum hFinite.toFinset nearTerm <=
        Finset.sum hFinite.toFinset (fun _ => (1 : Real)) :=
      Finset.sum_le_sum (fun p hp => by
        have hpWindow := (hFinite.mem_toFinset).mp hp
        change abs (T - (symmetricCompletedZeroValue p).im) < 1
          at hpWindow
        dsimp [nearTerm]
        rw [if_pos hpWindow]
        have hZeroReUpper : (symmetricCompletedZeroValue p).re < 1 :=
          (symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p).2
        have hExactRe :
            ((((2 : Real) : Complex) +
              (T : Complex) * Complex.I -
                symmetricCompletedZeroValue p)).re =
              2 - (symmetricCompletedZeroValue p).re := by
          norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re]
        have hDenRe :
            1 < ((((2 : Real) : Complex) +
              (T : Complex) * Complex.I -
                symmetricCompletedZeroValue p)).re := by
          rw [hExactRe]
          linarith
        have hNormLower :
            1 <= norm (((2 : Real) : Complex) +
              (T : Complex) * Complex.I -
                symmetricCompletedZeroValue p) := by
          have hAbsRe :
              1 <= abs ((((2 : Real) : Complex) +
                (T : Complex) * Complex.I -
                  symmetricCompletedZeroValue p)).re := by
            rw [abs_of_pos (lt_trans (by norm_num) hDenRe)]
            exact hDenRe.le
          exact hAbsRe.trans (Complex.abs_re_le_norm _)
        calc
          norm (1 / (((2 : Real) : Complex) +
              (T : Complex) * Complex.I -
                symmetricCompletedZeroValue p)) =
              1 / norm (((2 : Real) : Complex) +
                (T : Complex) * Complex.I -
                  symmetricCompletedZeroValue p) := by
            rw [norm_div, norm_one]
          _ <= 1 / (1 : Real) :=
            one_div_le_one_div_of_le (by norm_num) hNormLower
          _ = 1 := by norm_num)
    _ = (hFinite.toFinset.card : Real) := by simp
    _ = ((zeroHeightWindow (chi := chi) T).ncard : Real) := by
      rw [Set.ncard_eq_toFinset_card _ hFinite]
    _ <= C * (Real.log N + Real.log (abs T + 2)) := hCardBound

end BombieriVinogradov.SiegelWalfisz
