import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Complex representations of the real Mangoldt sums

These exact finite-sum transports connect the real discrepancy vocabulary
to the complex character expansion without changing endpoints or weights.
-/
set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem ofReal_psiGlobal (x : Nat) :
    (psiGlobal x : Complex) =
      Finset.sum (Finset.Icc 1 x) (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) := by
  rw [psiGlobal, Complex.ofReal_sum]

theorem ofReal_psiProgression (x N : Nat) (a : ZMod N) :
    (psiProgression x N a : Complex) =
      Finset.sum (Finset.Icc 1 x) (fun n =>
        if a = (n : ZMod N) then (ArithmeticFunction.vonMangoldt n : Complex) else 0) := by
  rw [psiProgression, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases h : a = (n : ZMod N)
  case pos => simp only [if_pos h]
  case neg => simp only [if_neg h, Complex.ofReal_zero]

end BombieriVinogradov.WeightedBombieriVinogradov
