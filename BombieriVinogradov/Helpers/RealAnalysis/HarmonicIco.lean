import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum

/-!
# Harmonic domination of a positive half-open range

This module compares the reciprocal sum over one through K-1 with the
standard harmonic number at K.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.RealAnalysis

theorem sum_one_div_Ico_le_harmonic (K : Nat) :
    Finset.sum (Finset.Ico 1 K) (fun k : Nat => 1 / (k : Real)) <=
      (harmonic K : Real) := by
  calc
    Finset.sum (Finset.Ico 1 K) (fun k : Nat => 1 / (k : Real)) <=
        Finset.sum (Finset.Icc 1 K) (fun k : Nat => 1 / (k : Real)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk =>
          have hkData := Finset.mem_Ico.mp hk
          Finset.mem_Icc.mpr
            (And.intro hkData.1 (Nat.le_of_lt hkData.2)))
        (fun k hk hnot =>
          one_div_nonneg.mpr (Nat.cast_nonneg k))
    _ = (harmonic K : Real) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]

end BombieriVinogradov.RealAnalysis
