import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite Schur bound

This is the finite real-matrix estimate used to control the Gram kernel in the
dual form of the additive large sieve.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- A nonnegative symmetric kernel is bounded on squared vectors by its largest row sum. -/
theorem schurBound {ι : Type*} [Fintype ι] (k : ι -> ι -> Real)
    (hk : ∀ i j, 0 <= k i j) (hsymm : ∀ i j, k i j = k j i)
    {B : Real} (hrow : ∀ i, ∑ j, k i j <= B) (b : ι -> Real) :
    ∑ i, ∑ j, b i * b j * k i j <= B * ∑ i, b i ^ 2 := by
  classical
  have hpoint (i j : ι) :
      2 * (b i * b j * k i j) <= b i ^ 2 * k i j + b j ^ 2 * k i j := by
    have hab : 2 * (b i * b j) <= b i ^ 2 + b j ^ 2 := by
      nlinarith [sq_nonneg (b i - b j)]
    nlinarith [mul_le_mul_of_nonneg_right hab (hk i j)]
  have hcol (j : ι) : ∑ i, k i j <= B := by
    calc
      ∑ i, k i j = ∑ i, k j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsymm i j
      _ <= B := hrow j
  have hdouble :
      2 * (∑ i, ∑ j, b i * b j * k i j) <=
        2 * (B * ∑ i, b i ^ 2) := by
    calc
      2 * (∑ i, ∑ j, b i * b j * k i j) =
          ∑ i, ∑ j, 2 * (b i * b j * k i j) := by
        simp_rw [Finset.mul_sum]
      _ <= ∑ i, ∑ j, (b i ^ 2 * k i j + b j ^ 2 * k i j) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
      _ = (∑ i, b i ^ 2 * ∑ j, k i j) +
          (∑ i, ∑ j, b j ^ 2 * k i j) := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (∑ i, b i ^ 2 * ∑ j, k i j) +
          (∑ j, b j ^ 2 * ∑ i, k i j) := by
        congr 1
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ <= (∑ i, b i ^ 2 * B) + (∑ j, b j ^ 2 * B) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (b i))
        · exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg (b j))
      _ = 2 * (B * ∑ i, b i ^ 2) := by
        simp_rw [← Finset.sum_mul]
        ring
  linarith

/-- Finset-indexed Schur bound, avoiding a global `Fintype` instance. -/
theorem schurBoundFinset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (k : ι -> ι -> Real) (hk : ∀ i ∈ s, ∀ j ∈ s, 0 <= k i j)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, k i j = k j i)
    {B : Real} (hrow : ∀ i ∈ s, ∑ j ∈ s, k i j <= B) (b : ι -> Real) :
    ∑ i ∈ s, ∑ j ∈ s, b i * b j * k i j <=
      B * ∑ i ∈ s, b i ^ 2 := by
  have hpoint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      2 * (b i * b j * k i j) <= b i ^ 2 * k i j + b j ^ 2 * k i j := by
    have hab : 2 * (b i * b j) <= b i ^ 2 + b j ^ 2 := by
      nlinarith [sq_nonneg (b i - b j)]
    nlinarith [mul_le_mul_of_nonneg_right hab (hk i hi j hj)]
  have hcol (j : ι) (hj : j ∈ s) : ∑ i ∈ s, k i j <= B := by
    calc
      ∑ i ∈ s, k i j = ∑ i ∈ s, k j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsymm i hi j hj
      _ <= B := hrow j hj
  have hdouble :
      2 * (∑ i ∈ s, ∑ j ∈ s, b i * b j * k i j) <=
        2 * (B * ∑ i ∈ s, b i ^ 2) := by
    calc
      2 * (∑ i ∈ s, ∑ j ∈ s, b i * b j * k i j) =
          ∑ i ∈ s, ∑ j ∈ s, 2 * (b i * b j * k i j) := by
        simp_rw [Finset.mul_sum]
      _ <= ∑ i ∈ s, ∑ j ∈ s,
          (b i ^ 2 * k i j + b j ^ 2 * k i j) := by
        exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
          hpoint i hi j hj
      _ = (∑ i ∈ s, b i ^ 2 * ∑ j ∈ s, k i j) +
          (∑ i ∈ s, ∑ j ∈ s, b j ^ 2 * k i j) := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (∑ i ∈ s, b i ^ 2 * ∑ j ∈ s, k i j) +
          (∑ j ∈ s, b j ^ 2 * ∑ i ∈ s, k i j) := by
        congr 1
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ <= (∑ i ∈ s, b i ^ 2 * B) + (∑ j ∈ s, b j ^ 2 * B) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg (b i))
        · exact Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hcol j hj) (sq_nonneg (b j))
      _ = 2 * (B * ∑ i ∈ s, b i ^ 2) := by
        simp_rw [← Finset.sum_mul]
        ring
  linarith

end BombieriVinogradov.LargeSieve
