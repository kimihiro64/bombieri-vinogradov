import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandSumSplit
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedPositiveBandHarmonicBound
import BombieriVinogradov.Helpers.RealAnalysis.LogQuadraticAbsorption
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Ring

/-!
# Complete retained reciprocal-zero cutoff estimate
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_norm_one_div_retainedCriticalZeroIndices_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} (hT : 0 < T) (exceptional : Option Complex)
    {C0 C1 : Real} (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (hN : 3 <= N)
    (hZero :
      Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
          (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        C0 * (Real.log N + 2) ^ 2)
    (hPositive : forall k : Nat, 1 <= k ->
      Finset.sum (retainedCriticalZeroBand chi T exceptional k)
          (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        C1 * (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) :
    Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
      (4 * C0 + C1) *
        (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 := by
  have hCeilPos : 0 < Nat.ceil T := (Nat.ceil_pos).2 hT
  have hCeil : 1 <= Nat.ceil T := hCeilPos
  have hLowScale :=
    BombieriVinogradov.RealAnalysis.log_nat_add_two_sq_le_four_mul_endpoint_sq
      hN hCeil
  have hLow :
      Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
          (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        4 * C0 *
          (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 := by
    calc
      Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
          (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        C0 * (Real.log N + 2) ^ 2 := hZero
      _ <= C0 * (4 *
          (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hLowScale hC0
      _ = 4 * C0 *
          (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 := by
        ring
  have hPositiveSum :
      Finset.sum (Finset.Ico 1 (Nat.ceil T)) (fun k =>
          Finset.sum (retainedCriticalZeroBand chi T exceptional k)
            (fun p => norm (1 / symmetricCompletedZeroValue p))) <=
        Finset.sum (Finset.Ico 1 (Nat.ceil T)) (fun k : Nat =>
          C1 * (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hPositive k (Finset.mem_Ico.mp hk).1
  have hHarmonic :=
    sum_scaled_log_add_div_Ico_le_sq hC1 hN (Nat.ceil T)
  rw [sum_norm_one_div_retainedCriticalZeroIndices_eq_bands hT exceptional]
  calc
    Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
          (fun p => norm (1 / symmetricCompletedZeroValue p)) +
        Finset.sum (Finset.Ico 1 (Nat.ceil T)) (fun k =>
          Finset.sum (retainedCriticalZeroBand chi T exceptional k)
            (fun p => norm (1 / symmetricCompletedZeroValue p))) <=
      4 * C0 *
          (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 +
        Finset.sum (Finset.Ico 1 (Nat.ceil T)) (fun k : Nat =>
          C1 * (Real.log N + Real.log ((k : Real) + 2)) / (k : Real)) :=
      add_le_add hLow hPositiveSum
    _ <= 4 * C0 *
          (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 +
        C1 *
          (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 :=
      add_le_add le_rfl hHarmonic
    _ = (4 * C0 + C1) *
        (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 := by
      ring

end BombieriVinogradov.SiegelWalfisz
