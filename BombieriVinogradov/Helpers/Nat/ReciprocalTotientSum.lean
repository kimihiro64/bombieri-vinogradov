import BombieriVinogradov.Helpers.Nat.DivisorHarmonicBound
import BombieriVinogradov.Helpers.RealAnalysis.HarmonicIcc
import BombieriVinogradov.Helpers.RealAnalysis.ReciprocalTotient
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# A logarithmic-square reciprocal-totient summation bound

The divisor comparison gives a harmonic square with coefficient one.
The logarithmic corollary retains that coefficient for every natural cutoff.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem sum_one_div_totient_le_sum_one_div_sq (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
      (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
        Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) :=
      Finset.sum_le_sum (fun n hn => one_div_totient_le_divisor_card_div
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
    _ <= (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 :=
      sum_divisor_card_div_le_sum_one_div_sq Q

theorem sum_one_div_totient_le_one_add_log_sq (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
      (1 + Real.log (Q : Real)) ^ 2 := by
  have hUpper := RealAnalysis.sum_one_div_Icc_le_one_add_log Q
  have hNonneg : 0 <= Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) :=
    Finset.sum_nonneg (fun n _ => one_div_nonneg.mpr (Nat.cast_nonneg n))
  have hSquare :
      Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) *
        Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) <=
      (1 + Real.log (Q : Real)) * (1 + Real.log (Q : Real)) :=
    (mul_le_mul_of_nonneg_right hUpper hNonneg).trans
      (mul_le_mul_of_nonneg_left hUpper (hNonneg.trans hUpper))
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
        (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 :=
      sum_one_div_totient_le_sum_one_div_sq Q
    _ = Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) *
        Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) := by ring
    _ <= (1 + Real.log (Q : Real)) * (1 + Real.log (Q : Real)) := hSquare
    _ = (1 + Real.log (Q : Real)) ^ 2 := by ring

end BombieriVinogradov
