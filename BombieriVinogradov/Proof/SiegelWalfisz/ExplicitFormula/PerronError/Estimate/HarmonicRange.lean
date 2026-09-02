import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic sums of integer distances

This module evaluates the lower and upper distance kernels around a natural
endpoint by reflecting or translating a finite interval.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

/-- Distances below `x` enumerate the positive integers from one through `x`. -/
theorem lower_distance_sum_eq_harmonic (x : Nat) :
    (Finset.sum (range x) (fun n : Nat =>
      1 / (((x - n : Nat) : Real)))) = (harmonic x : Real) := by
  calc
    Finset.sum (range x) (fun n : Nat =>
        1 / (((x - n : Nat) : Real))) =
      Finset.sum (range x) (fun n : Nat =>
        1 / ((((x - 1 - n) + 1 : Nat) : Real))) := by
      apply sum_congr rfl
      intro n hn
      have hnx : n < x := mem_range.mp hn
      congr 3
      omega
    _ = Finset.sum (range x) (fun k : Nat =>
        1 / (((k + 1 : Nat) : Real))) :=
      sum_range_reflect (fun k : Nat => 1 / (((k + 1 : Nat) : Real))) x
    _ = (harmonic x : Real) := by
      rw [harmonic, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Distances above `x` through `2 * x` enumerate the same harmonic range. -/
theorem upper_distance_sum_eq_harmonic (x : Nat) :
    (Finset.sum (Ico (x + 1) (2 * x + 1)) (fun n : Nat =>
      1 / (((n - x : Nat) : Real)))) = (harmonic x : Real) := by
  rw [sum_Ico_eq_sum_range]
  have hLength : 2 * x + 1 - (x + 1) = x := by omega
  rw [hLength]
  calc
    Finset.sum (range x) (fun k : Nat =>
        1 / (((x + 1 + k - x : Nat) : Real))) =
      Finset.sum (range x) (fun k : Nat =>
        1 / (((k + 1 : Nat) : Real))) := by
      apply sum_congr rfl
      intro k hk
      congr 3
      omega
    _ = (harmonic x : Real) := by
      rw [harmonic, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]

end BombieriVinogradov.SiegelWalfisz
