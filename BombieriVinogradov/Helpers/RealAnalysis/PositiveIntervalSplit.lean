import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Splitting nonnegative sums at an arbitrary natural cutoff

The lower partial sum may extend beyond the original endpoint. Nonnegativity
makes the resulting inequality valid in either cutoff ordering.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- A nonnegative positive-interval sum is bounded by a cutoff sum plus its upper tail. -/
theorem sum_Icc_le_sum_Icc_add_sum_Ioc (F : Nat -> Real) (hF : forall n, 0 <= F n)
    (R Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) F <=
      Finset.sum (Finset.Icc 1 R) F + Finset.sum (Finset.Ioc R Q) F := by
  have hCover : forall n, (Finset.Icc 1 Q : Set Nat) n ->
      ((Union.union (Finset.Icc 1 R) (Finset.Ioc R Q) : Finset Nat) : Set Nat) n := by
    intro n hn
    have hAlternatives : Or ((Finset.Icc 1 R : Set Nat) n)
        ((Finset.Ioc R Q : Set Nat) n) := by
      by_cases hnR : n <= R
      case pos =>
        exact Or.inl (Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp hn).1 hnR))
      case neg =>
        exact Or.inr (Finset.mem_Ioc.mpr (And.intro (Nat.lt_of_not_ge hnR)
          (Finset.mem_Icc.mp hn).2))
    exact (Finset.mem_union (a := n) (s := Finset.Icc 1 R)
      (t := Finset.Ioc R Q)).mpr hAlternatives
  have hDisjoint : Disjoint (Finset.Icc 1 R) (Finset.Ioc R Q) :=
    Finset.disjoint_left.mpr (fun _ hn hnTail =>
      (Nat.not_lt_of_ge (Finset.mem_Icc.mp hn).2) (Finset.mem_Ioc.mp hnTail).1)
  calc
    Finset.sum (Finset.Icc 1 Q) F <=
        Finset.sum (Union.union (Finset.Icc 1 R) (Finset.Ioc R Q)) F :=
      Finset.sum_le_sum_of_subset_of_nonneg hCover (fun n _ _ => hF n)
    _ = Finset.sum (Finset.Icc 1 R) F + Finset.sum (Finset.Ioc R Q) F :=
      Finset.sum_union hDisjoint

end BombieriVinogradov.RealAnalysis
