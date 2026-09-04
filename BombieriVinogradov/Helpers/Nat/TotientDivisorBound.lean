import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors

/-!
# Elementary comparison of a modulus with its totient

The totients of its divisors sum to the modulus, and each divides
the positive ambient totient. Their count therefore gives an upper bound.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem le_totient_mul_card_divisors {n : Nat} (hn : 0 < n) :
    n <= n.totient * n.divisors.card := by
  calc
    n = Finset.sum n.divisors Nat.totient := (Nat.sum_totient n).symm
    _ <= Finset.sum n.divisors (fun _ => n.totient) :=
      Finset.sum_le_sum (fun d hd => Nat.le_of_dvd (Nat.totient_pos.mpr hn)
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
    _ = n.totient * n.divisors.card := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

end BombieriVinogradov
