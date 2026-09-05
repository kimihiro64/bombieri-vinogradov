import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import BombieriVinogradov.Proof.PrimeCountingConversion.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Higher-prime-power errors

The progression error is a nonnegative sub-sum of the global psi-minus-theta
error, which is bounded by Mathlib's Chebyshev estimate.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The global project psi sum is Mathlib's Chebyshev psi at a natural endpoint. -/
theorem psiGlobal_eq_chebyshevPsi (N : Nat) :
    WeightedBombieriVinogradov.psiGlobal N = Chebyshev.psi (N : Real) := by
  unfold WeightedBombieriVinogradov.psiGlobal Chebyshev.psi
  simp only [Nat.floor_natCast]
  apply Finset.sum_congr
  exact Finset.Icc_succ_left_eq_Ioc 0 N
  intro n hn
  rfl

/-- The project theta sum is Mathlib's Chebyshev theta at a natural endpoint. -/
theorem thetaGlobalNat_eq_chebyshevTheta (N : Nat) :
    thetaGlobalNat N = Chebyshev.theta (N : Real) := by
  unfold thetaGlobalNat Chebyshev.theta
  simp only [Nat.floor_natCast, Finset.sum_filter]
  apply Finset.sum_congr
  exact Finset.Icc_succ_left_eq_Ioc 0 N
  intro n hn
  rfl

/-- Progression higher-prime-power mass is nonnegative and no larger than the global mass. -/
theorem progression_primePower_error_bounds (N q : Nat) (a : ZMod q) :
    And (0 <= WeightedBombieriVinogradov.psiProgression N q a -
      thetaProgressionNat N q a)
      (WeightedBombieriVinogradov.psiProgression N q a - thetaProgressionNat N q a <=
        WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N) := by
  have hProgression : WeightedBombieriVinogradov.psiProgression N q a -
      thetaProgressionNat N q a =
        Finset.sum (Finset.Icc 1 N) (fun n =>
          if And (Not n.Prime) (a = (n : ZMod q))
          then ArithmeticFunction.vonMangoldt n else 0) := by
    unfold WeightedBombieriVinogradov.psiProgression thetaProgressionNat
    calc
      Finset.sum (Finset.Icc 1 N)
          (fun n => if a = (n : ZMod q) then ArithmeticFunction.vonMangoldt n else 0) -
          Finset.sum (Finset.Icc 1 N) (fun n =>
            if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) =
        Finset.sum (Finset.Icc 1 N) (fun n =>
          (if a = (n : ZMod q) then ArithmeticFunction.vonMangoldt n else 0) -
            (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0)) := by
          rw [Finset.sum_sub_distrib]
      _ = Finset.sum (Finset.Icc 1 N) (fun n =>
          if And (Not n.Prime) (a = (n : ZMod q))
          then ArithmeticFunction.vonMangoldt n else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hp : n.Prime
        case pos => simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp, eq_comm]
        case neg => simp [hp, eq_comm]
  have hGlobal : WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N =
      Finset.sum (Finset.Icc 1 N) (fun n =>
        if Not n.Prime then ArithmeticFunction.vonMangoldt n else 0) := by
    unfold WeightedBombieriVinogradov.psiGlobal thetaGlobalNat
    calc
      Finset.sum (Finset.Icc 1 N) ArithmeticFunction.vonMangoldt -
          Finset.sum (Finset.Icc 1 N)
            (fun n => if n.Prime then Real.log (n : Real) else 0) =
        Finset.sum (Finset.Icc 1 N) (fun n =>
          ArithmeticFunction.vonMangoldt n -
            (if n.Prime then Real.log (n : Real) else 0)) := by
          rw [Finset.sum_sub_distrib]
      _ = Finset.sum (Finset.Icc 1 N) (fun n =>
          if Not n.Prime then ArithmeticFunction.vonMangoldt n else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hp : n.Prime
        case pos => simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
        case neg => simp [hp]
  rw [hProgression, hGlobal]
  refine And.intro (Finset.sum_nonneg (fun n hn => by
    split <;> positivity)) ?_
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  case pos => simp [hp]
  case neg =>
    by_cases ha : a = (n : ZMod q)
    case pos => simp [hp, ha]
    case neg => simp [hp, ha, ArithmeticFunction.vonMangoldt_nonneg]

/-- Progression higher-prime-power mass has the same explicit global bound. -/
theorem progression_primePower_error_le {N q : Nat} (a : ZMod q) (hN : 1 <= N) :
    WeightedBombieriVinogradov.psiProgression N q a - thetaProgressionNat N q a <=
      2 * Real.sqrt (N : Real) * Real.log (N : Real) := by
  have hGlobal := (progression_primePower_error_bounds N q a).2
  rw [psiGlobal_eq_chebyshevPsi, thetaGlobalNat_eq_chebyshevTheta] at hGlobal
  have hNRaw : (((1 : Nat) : Real) <= (N : Real)) := Nat.cast_le.mpr hN
  have hNReal : (1 : Real) <= (N : Real) := by simpa only [Nat.cast_one] using hNRaw
  exact hGlobal.trans (Chebyshev.psi_sub_theta_le hNReal)

end BombieriVinogradov.PrimeCountingConversion
