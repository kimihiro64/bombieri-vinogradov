import BombieriVinogradov.Helpers.Nat.BadPrimePowerDivisor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Integer-logarithmic bound for the noncoprime Mangoldt mass

Nonzero weights lie among divisors of N raised to the complete integer
cutoff. The von Mangoldt divisor identity evaluates the dominating sum.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem nonCoprimeMangoldtSum_le_natLog_mul_log
    {N : Nat} (hN : Ne N 0) (x : Nat) :
    Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
      ArithmeticFunction.vonMangoldt <=
        (Nat.log 2 x : Real) * Real.log N := by
  classical
  let s : Finset Nat := (Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N))
  have hPowerNe : Ne (N ^ Nat.log 2 x) 0 := pow_ne_zero _ hN
  have hCover : forall n : Nat,
      (s.filter (fun m => Ne (ArithmeticFunction.vonMangoldt m) 0) : Set Nat) n ->
        ((N ^ Nat.log 2 x).divisors : Set Nat) n := by
    intro n hn
    have hNonzeroData :
        And ((s : Set Nat) n) (Ne (ArithmeticFunction.vonMangoldt n) 0) :=
      (Finset.mem_filter (s := s) (a := n)
        (p := fun m : Nat => Ne (ArithmeticFunction.vonMangoldt m) 0)).mp hn
    have hBadData :
        And ((Finset.Icc 1 x : Set Nat) n) (Not (Nat.Coprime n N)) :=
      (Finset.mem_filter (s := Finset.Icc 1 x) (a := n)
        (p := fun m : Nat => Not (Nat.Coprime m N))).mp hNonzeroData.1
    have hnLe : n <= x := (Finset.mem_Icc.mp hBadData.1).2
    have hDiv := badPrimePower_dvd_level_pow_log hN hnLe hBadData.2
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hNonzeroData.2)
    exact Nat.mem_divisors.mpr (And.intro hDiv hPowerNe)
  change Finset.sum s ArithmeticFunction.vonMangoldt <= _
  calc
    Finset.sum s ArithmeticFunction.vonMangoldt =
        Finset.sum (s.filter (fun n => Ne (ArithmeticFunction.vonMangoldt n) 0))
          ArithmeticFunction.vonMangoldt :=
      (Finset.sum_filter_ne_zero s).symm
    _ <= Finset.sum (N ^ Nat.log 2 x).divisors ArithmeticFunction.vonMangoldt :=
      Finset.sum_le_sum_of_subset_of_nonneg hCover
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((N ^ Nat.log 2 x : Nat) : Real) := ArithmeticFunction.vonMangoldt_sum
    _ = (Nat.log 2 x : Real) * Real.log N := by
      rw [Nat.cast_pow, Real.log_pow]

end BombieriVinogradov
