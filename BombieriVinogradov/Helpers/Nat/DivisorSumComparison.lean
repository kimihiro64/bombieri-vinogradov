import BombieriVinogradov.Helpers.Nat.DivisorHyperbolaPairs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Sigma.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Comparing a divisor sum with a nonnegative square majorant

The divisor-to-factor-pair injection preserves every summand.
Only the majorant on the larger positive square must be nonnegative.
-/
set_option autoImplicit false

namespace BombieriVinogradov

theorem sum_divisors_le_sum_product (Q : Nat) (h g : Nat -> Nat -> Real)
    (hBound : forall n d : Nat, (Finset.Icc 1 Q : Set Nat) n ->
      (n.divisors : Set Nat) d -> h n d <= g d (n / d))
    (hNonneg : forall a b : Nat, (Finset.Icc 1 Q : Set Nat) a ->
      (Finset.Icc 1 Q : Set Nat) b -> 0 <= g a b) :
    Finset.sum (Finset.Icc 1 Q) (fun n => Finset.sum n.divisors (h n)) <=
      Finset.sum (Finset.Icc 1 Q) (fun a => Finset.sum (Finset.Icc 1 Q) (g a)) := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n => Finset.sum n.divisors (h n)) =
        Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
          (fun p : Sigma (fun _ : Nat => Nat) => h p.1 p.2) :=
      (Finset.sum_sigma (Finset.Icc 1 Q) Nat.divisors
        (fun p : Sigma (fun _ : Nat => Nat) => h p.1 p.2)).symm
    _ <= Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
        (fun p : Sigma (fun _ : Nat => Nat) => g p.2 (p.1 / p.2)) :=
      Finset.sum_le_sum (fun p hp =>
        hBound p.1 p.2 (Finset.mem_sigma.mp hp).1 (Finset.mem_sigma.mp hp).2)
    _ = Finset.sum ((Finset.sigma (Finset.Icc 1 Q) Nat.divisors).image
        (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2)))
        (fun z => g z.1 z.2) :=
      (Finset.sum_image (f := fun z : Prod Nat Nat => g z.1 z.2) (divisorSigma_pair_inj Q)).symm
    _ <= Finset.sum ((Finset.Icc 1 Q).product (Finset.Icc 1 Q))
        (fun z => g z.1 z.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr (fun p hp => divisorSigma_pair_mem_product p hp))
        (fun z hz _ => hNonneg z.1 z.2 (Finset.mem_product.mp hz).1
          (Finset.mem_product.mp hz).2)
    _ = Finset.sum (Finset.Icc 1 Q) (fun a => Finset.sum (Finset.Icc 1 Q) (g a)) :=
      Finset.sum_product (Finset.Icc 1 Q) (Finset.Icc 1 Q) (fun z : Prod Nat Nat => g z.1 z.2)

end BombieriVinogradov
