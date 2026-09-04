import BombieriVinogradov.Helpers.Nat.DivisorSumComparison
import BombieriVinogradov.Helpers.Nat.ReciprocalTotientSum
import BombieriVinogradov.Helpers.RealAnalysis.TotientProductWeight
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Weighted lifting from divisors to conductor moduli

Bound a nonnegative divisor weight averaged with reciprocal totients by the
same conductor weight times a reciprocal-totient sum, then a logarithmic square.
-/

set_option autoImplicit false

namespace BombieriVinogradov

/-- Lift a nonnegative divisor weight while retaining its conductor totient. -/
theorem sum_weighted_divisors_div_totient_le_product (Q : Nat) (F : Nat -> Real)
    (hF : forall n, 0 <= F n) :
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) <=
      (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
        Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k.totient : Real)) := by
  calc
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) =
        Finset.sum (Finset.Icc 1 Q)
          (fun n => Finset.sum n.divisors (fun d => F d / (n.totient : Real))) :=
      Finset.sum_congr rfl (fun n _ => Finset.sum_div n.divisors F (n.totient : Real))
    _ <= Finset.sum (Finset.Icc 1 Q) (fun d => Finset.sum (Finset.Icc 1 Q)
        (fun k => F d / (d.totient : Real) * (1 / (k.totient : Real)))) :=
      sum_divisors_le_sum_product Q
        (fun n d => F d / (n.totient : Real))
        (fun d k => F d / (d.totient : Real) * (1 / (k.totient : Real)))
        (fun n d hn hd => div_totient_le_divisor_quotient_weight
          (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
          (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd) (F d) (hF d))
        (fun a b _ _ => mul_nonneg (div_nonneg (hF a) (Nat.cast_nonneg a.totient))
          (one_div_nonneg.mpr (Nat.cast_nonneg b.totient)))
    _ = (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
        Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k.totient : Real)) :=
      (Finset.sum_mul_sum (Finset.Icc 1 Q) (Finset.Icc 1 Q)
        (fun d => F d / (d.totient : Real)) (fun k => 1 / (k.totient : Real))).symm

/-- A coefficient-one logarithmic-square cost for lifting conductor weights. -/
theorem sum_weighted_divisors_div_totient_le_log_sq (Q : Nat) (F : Nat -> Real)
    (hF : forall n, 0 <= F n) :
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) <=
      (1 + Real.log Q) ^ 2 *
        Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real)) := by
  have hNonneg : 0 <=
      Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real)) :=
    Finset.sum_nonneg (fun d _ => div_nonneg (hF d) (Nat.cast_nonneg d.totient))
  calc
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) <=
        (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
          Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k.totient : Real)) :=
      sum_weighted_divisors_div_totient_le_product Q F hF
    _ <= (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
        (1 + Real.log Q) ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_one_div_totient_le_one_add_log_sq Q) hNonneg
    _ = (1 + Real.log Q) ^ 2 *
        Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real)) :=
      mul_comm _ _

end BombieriVinogradov
