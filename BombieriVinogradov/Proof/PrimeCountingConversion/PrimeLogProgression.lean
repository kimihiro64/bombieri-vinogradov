import BombieriVinogradov.Proof.PrimeCountingConversion.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Progression prime-log weights

Prime logarithms cancel only at verified prime endpoints.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- Progression prime-log weights equal the finite progression prime count. -/
theorem sum_progressionPrimeLog_div_log {N q : Nat} (a : ZMod q) :
    Finset.sum (Finset.Icc 2 N) (fun n =>
      (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) /
        Real.log (n : Real)) = (primeProgressionNat N q a : Real) := by
  let P : Nat -> Prop := fun n => And n.Prime ((n : ZMod q) = a)
  have hSets : (Finset.Icc 2 N).filter P = (Finset.Icc 1 N).filter P := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    apply Iff.intro
    case mp =>
      intro h
      exact And.intro (And.intro (by linarith) h.1.2) h.2
    case mpr =>
      intro h
      exact And.intro (And.intro h.2.1.two_le h.1.2) h.2
  have hRewrite : Finset.sum (Finset.Icc 2 N) (fun n =>
      (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) /
        Real.log (n : Real)) = Finset.sum (Finset.Icc 2 N) (fun n =>
      if P n then Real.log (n : Real) / Real.log (n : Real) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : P n
    case pos => simp [P, h]
    case neg => simp [P, h]
  calc
    Finset.sum (Finset.Icc 2 N) (fun n =>
        (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) /
          Real.log (n : Real)) =
      Finset.sum ((Finset.Icc 2 N).filter P)
        (fun n => Real.log (n : Real) / Real.log (n : Real)) := by
          rw [hRewrite, Finset.sum_filter]
    _ = Finset.sum ((Finset.Icc 2 N).filter P) (fun n => (1 : Real)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnPrime := (Finset.mem_filter.mp hn).2.1
      have hLogPos : 0 < Real.log (n : Real) := by
        apply Real.log_pos
        have hnRaw : (((2 : Nat) : Real) <= (n : Real)) := Nat.cast_le.mpr hnPrime.two_le
        have hnTwo : (2 : Real) <= (n : Real) := by
          simpa only [Nat.cast_ofNat] using hnRaw
        linarith
      exact div_self (ne_of_gt hLogPos)
    _ = (((Finset.Icc 2 N).filter P).card : Real) := by simp
    _ = (((Finset.Icc 1 N).filter P).card : Real) := by rw [hSets]
    _ = (primeProgressionNat N q a : Real) := by rfl

end BombieriVinogradov.PrimeCountingConversion
