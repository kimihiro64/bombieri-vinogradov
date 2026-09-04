import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.DirichletCharacter.MangoldtPrimitiveDifference
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite-sum comparison with the primitive character

The triangle inequality reduces the Chebyshev-sum correction to precisely
the von Mangoldt mass on integers not coprime to the ambient modulus.
-/
set_option autoImplicit false

namespace BombieriVinogradov.VaughanMeanValue

theorem norm_psiCharacterSum_sub_primitive_le_mangoldt
    {N : Nat} (chi : _root_.DirichletCharacter Complex N) (x : Nat) :
    norm (psiCharacterSum x N chi -
      psiCharacterSum x chi.conductor chi.primitiveCharacter) <=
        Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
          ArithmeticFunction.vonMangoldt := by
  classical
  unfold psiCharacterSum
  rw [<- Finset.sum_sub_distrib]
  calc
    norm (Finset.sum (Finset.Icc 1 x) (fun n =>
        (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N) -
          (ArithmeticFunction.vonMangoldt n : Complex) *
            chi.primitiveCharacter (n : ZMod chi.conductor))) <=
        Finset.sum (Finset.Icc 1 x) (fun n => norm
          ((ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N) -
            (ArithmeticFunction.vonMangoldt n : Complex) *
              chi.primitiveCharacter (n : ZMod chi.conductor))) := norm_sum_le _ _
    _ <= Finset.sum (Finset.Icc 1 x) (fun n =>
        if Nat.Coprime n N then 0 else ArithmeticFunction.vonMangoldt n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [<- mul_sub]
      exact DirichletCharacter.norm_mangoldt_mul_natCast_sub_primitive_le chi n
    _ = Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
        ArithmeticFunction.vonMangoldt := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : Nat.Coprime n N
      case pos =>
        have hh : Not (Not (Nat.Coprime n N)) := fun hn => hn h
        rw [if_pos h, if_neg hh]
      case neg => rw [if_neg h, if_pos h]

end BombieriVinogradov.VaughanMeanValue
