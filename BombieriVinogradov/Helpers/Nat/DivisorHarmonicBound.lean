import BombieriVinogradov.Helpers.Nat.DivisorHyperbolaPairs
import BombieriVinogradov.Helpers.RealAnalysis.DivisorReciprocal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Sigma.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Divisor reciprocal sum bounded by a harmonic square

Inject the divisor hyperbola into the positive square and enlarge
the nonnegative sum. The rectangular sum factors into two harmonic sums.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem sum_divisor_card_div_le_sum_one_div_sq (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) <=
      (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 := by
  have hExpand :
      Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) =
        Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
          (fun p : Sigma (fun _ : Nat => Nat) => 1 / (p.1 : Real)) := by
    rw [Finset.sum_sigma (Finset.Icc 1 Q) Nat.divisors
      (fun p : Sigma (fun _ : Nat => Nat) => 1 / (p.1 : Real))]
    apply Finset.sum_congr rfl
    intro n _hn
    change (n.divisors.card : Real) / (n : Real) =
      Finset.sum n.divisors (fun _ => 1 / (n : Real))
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hSubset : forall z : Prod Nat Nat,
      ((Finset.sigma (Finset.Icc 1 Q) Nat.divisors).image
        (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2)) :
          Set (Prod Nat Nat)) z ->
      ((Finset.Icc 1 Q).product (Finset.Icc 1 Q) : Set (Prod Nat Nat)) z := by
    intro z hz
    have hData := Finset.mem_image.mp hz
    rw [<- hData.choose_spec.2]
    exact divisorSigma_pair_mem_product hData.choose hData.choose_spec.1
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) =
        Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
          (fun p : Sigma (fun _ : Nat => Nat) => 1 / (p.1 : Real)) := hExpand
    _ = Finset.sum ((Finset.sigma (Finset.Icc 1 Q) Nat.divisors).image
          (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2)))
        (fun z => 1 / (z.1 : Real) * (1 / (z.2 : Real))) := by
      rw [Finset.sum_image (divisorSigma_pair_inj Q)]
      apply Finset.sum_congr rfl
      intro p hp
      exact one_div_nat_eq_divisor_reciprocal_product
        (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).2)
    _ <= Finset.sum ((Finset.Icc 1 Q).product (Finset.Icc 1 Q))
        (fun z => 1 / (z.1 : Real) * (1 / (z.2 : Real))) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun z _ _ =>
        mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg z.1))
          (one_div_nonneg.mpr (Nat.cast_nonneg z.2)))
    _ = Finset.sum (Finset.Icc 1 Q) (fun a => Finset.sum (Finset.Icc 1 Q)
        (fun b => 1 / (a : Real) * (1 / (b : Real)))) :=
      Finset.sum_product (Finset.Icc 1 Q) (Finset.Icc 1 Q)
        (fun z : Prod Nat Nat => 1 / (z.1 : Real) * (1 / (z.2 : Real)))
    _ = (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 := by
      rw [<- Finset.sum_mul_sum]
      ring

end BombieriVinogradov
