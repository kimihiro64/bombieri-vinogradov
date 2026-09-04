import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic

/-!
# Reciprocal product for a divisor and its quotient

The identity is total, including zero, because divisibility gives
the exact natural factorization before passage to real reciprocals.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem one_div_nat_eq_divisor_reciprocal_product {n d : Nat} (hd : Dvd.dvd d n) :
    1 / (n : Real) = 1 / (d : Real) * (1 / ((n / d : Nat) : Real)) := by
  rw [one_div_mul_one_div, <- Nat.cast_mul, Nat.mul_div_cancel' hd]

end BombieriVinogradov
