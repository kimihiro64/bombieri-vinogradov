import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Reciprocal totient weight on a positive product

Totient super-multiplicativity gives the reciprocal comparison
without requiring the two factors to be coprime.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem one_div_totient_mul_le_product {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    1 / ((a * b).totient : Real) <=
      1 / (a.totient : Real) * (1 / (b.totient : Real)) := by
  have hPositive : (0 : Real) < (a.totient : Real) * (b.totient : Real) :=
    mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr ha))
      (Nat.cast_pos.mpr (Nat.totient_pos.mpr hb))
  have hCast : ((a.totient * b.totient : Nat) : Real) <= ((a * b).totient : Real) :=
    Nat.cast_le.mpr (Nat.totient_super_multiplicative a b)
  rw [Nat.cast_mul] at hCast
  calc
    1 / ((a * b).totient : Real) <= 1 / ((a.totient : Real) * (b.totient : Real)) :=
      one_div_le_one_div_of_le hPositive hCast
    _ = 1 / (a.totient : Real) * (1 / (b.totient : Real)) :=
      (one_div_mul_one_div (a := (a.totient : Real)) (b := (b.totient : Real))).symm

theorem div_totient_le_divisor_quotient_weight {n d : Nat}
    (hn : 0 < n) (hd : Dvd.dvd d n) (hdPos : 0 < d) (w : Real) (hw : 0 <= w) :
    w / (n.totient : Real) <=
      w / (d.totient : Real) * (1 / ((n / d).totient : Real)) := by
  have hQuotientPos := Nat.div_pos (Nat.le_of_dvd hn hd) hdPos
  have hWeight := one_div_totient_mul_le_product hdPos hQuotientPos
  rw [Nat.mul_div_cancel' hd] at hWeight
  calc
    w / (n.totient : Real) = w * (1 / (n.totient : Real)) := by ring
    _ <= w * (1 / (d.totient : Real) * (1 / ((n / d).totient : Real))) :=
      mul_le_mul_of_nonneg_left hWeight hw
    _ = w / (d.totient : Real) * (1 / ((n / d).totient : Real)) := by ring

end BombieriVinogradov
