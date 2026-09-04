import BombieriVinogradov.Helpers.Nat.TotientDivisorBound
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp

/-!
# Reciprocal totient bounded by the divisor count

The integer totient comparison is transported through two positive
divisions, with both denominator signs explicit.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem one_div_totient_le_divisor_card_div {n : Nat} (hn : 0 < n) :
    1 / (n.totient : Real) <= (n.divisors.card : Real) / (n : Real) := by
  have hnReal : (0 : Real) < (n : Real) := Nat.cast_pos.mpr hn
  have hPhi : (0 : Real) < (n.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hn)
  have hCast : (n : Real) <= ((n.totient * n.divisors.card : Nat) : Real) :=
    Nat.cast_le.mpr (le_totient_mul_card_divisors hn)
  rw [Nat.cast_mul] at hCast
  have hFirst := div_le_div_of_nonneg_right hCast hPhi.le
  have hCancel :
      ((n.totient : Real) * (n.divisors.card : Real)) / (n.totient : Real) =
        (n.divisors.card : Real) := by field_simp
  rw [hCancel] at hFirst
  have hSecond := div_le_div_of_nonneg_right hFirst hnReal.le
  have hNormalize :
      (n : Real) / (n.totient : Real) / (n : Real) = 1 / (n.totient : Real) := by field_simp
  rw [hNormalize] at hSecond
  exact hSecond

end BombieriVinogradov
