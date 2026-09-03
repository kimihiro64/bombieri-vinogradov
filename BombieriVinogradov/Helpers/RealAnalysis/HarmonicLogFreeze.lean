import BombieriVinogradov.Helpers.RealAnalysis.HarmonicIco
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Freezing a logarithmic numerator in a harmonic sum

This module bounds the varying logarithmic numerator on a positive half-open
range by its endpoint value and factors it from the reciprocal sum.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.RealAnalysis

theorem sum_log_add_div_Ico_le_mul_harmonic
    {L : Real} (hL : 0 <= L) (K : Nat) :
    Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
        (L + Real.log ((k : Real) + 2)) / (k : Real)) <=
      (L + Real.log ((K : Real) + 2)) * (harmonic K : Real) := by
  have hKNonneg : 0 <= (K : Real) := Nat.cast_nonneg K
  have hLogEndpointNonneg :
      0 <= Real.log ((K : Real) + 2) :=
    Real.log_nonneg (by linarith)
  have hScaleNonneg : 0 <= L + Real.log ((K : Real) + 2) := by
    linarith
  calc
    Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
        (L + Real.log ((k : Real) + 2)) / (k : Real)) <=
      Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
        (L + Real.log ((K : Real) + 2)) * (1 / (k : Real))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkData := Finset.mem_Ico.mp hk
      have hkLeNat : k <= K := Nat.le_of_lt hkData.2
      have hkLeReal : (k : Real) <= (K : Real) :=
        (Nat.cast_le).2 hkLeNat
      have hkNonneg : 0 <= (k : Real) := Nat.cast_nonneg k
      have hKArgPos : 0 < (k : Real) + 2 := by
        linarith
      have hArgLe : (k : Real) + 2 <= (K : Real) + 2 := by
        linarith
      have hLogLe :
          Real.log ((k : Real) + 2) <=
            Real.log ((K : Real) + 2) :=
        Real.log_le_log hKArgPos hArgLe
      have hNumerator :
          L + Real.log ((k : Real) + 2) <=
            L + Real.log ((K : Real) + 2) := by
        linarith
      have hkNat : 0 < k := Nat.zero_lt_of_lt hkData.1
      have hkReal : 0 < (k : Real) := (Nat.cast_pos).2 hkNat
      have hDiv :
          (L + Real.log ((k : Real) + 2)) / (k : Real) <=
            (L + Real.log ((K : Real) + 2)) / (k : Real) :=
        div_le_div_of_nonneg_right hNumerator (le_of_lt hkReal)
      calc
        (L + Real.log ((k : Real) + 2)) / (k : Real) <=
            (L + Real.log ((K : Real) + 2)) / (k : Real) := hDiv
        _ = (L + Real.log ((K : Real) + 2)) *
            (1 / (k : Real)) := by ring
    _ = (L + Real.log ((K : Real) + 2)) *
        Finset.sum (Finset.Ico 1 K) (fun k : Nat => 1 / (k : Real)) := by
      rw [Finset.mul_sum]
    _ <= (L + Real.log ((K : Real) + 2)) * (harmonic K : Real) :=
      mul_le_mul_of_nonneg_left (sum_one_div_Ico_le_harmonic K)
        hScaleNonneg

end BombieriVinogradov.RealAnalysis
