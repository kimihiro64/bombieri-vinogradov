import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dividing a weighted power estimate

This module isolates the positive-denominator algebra that converts the
weighted residue estimate into a direct negative-power lower bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem weighted_rpow_transfer {prefactor bound base exponent delta epsilon value : ℝ}
    (hprefactor : 0 < prefactor) (hbound : 0 < bound) (hbase : 1 ≤ base)
    (hsum : exponent + delta ≤ epsilon)
    (hweighted : prefactor * base ^ (-exponent) ≤
      bound * base ^ delta * value) :
    (prefactor / bound) * base ^ (-epsilon) ≤ value := by
  have hbasePos : 0 < base := zero_lt_one.trans_le hbase
  have hpowerDelta : 0 < base ^ delta := Real.rpow_pos_of_pos hbasePos delta
  have hdenominator : 0 < bound * base ^ delta := mul_pos hbound hpowerDelta
  have hdivided :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) ≤ value := by
    rw [div_le_iff₀ hdenominator]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hquotient :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) =
        (prefactor / bound) * base ^ (-(exponent + delta)) := by
    rw [show -(exponent + delta) = -exponent + -delta by ring,
      Real.rpow_add hbasePos, Real.rpow_neg hbasePos.le]
    field_simp
    rw [← Real.rpow_add hbasePos]
    norm_num
  have hpower : base ^ (-epsilon) ≤ base ^ (-(exponent + delta)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  calc
    (prefactor / bound) * base ^ (-epsilon) ≤
        (prefactor / bound) * base ^ (-(exponent + delta)) :=
      mul_le_mul_of_nonneg_left hpower (div_nonneg hprefactor.le hbound.le)
    _ = (prefactor * base ^ (-exponent)) / (bound * base ^ delta) :=
      hquotient.symm
    _ ≤ value := hdivided

end BombieriVinogradov.SiegelWalfisz
