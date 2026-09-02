import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.HarmonicRange
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.NearBounds

/-!
# Central-range harmonic sums

This module evaluates both finite-support near-range bounds as the common
coefficient times the harmonic number at `x`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

/-- The lower near-range bound sums to the expected harmonic factor. -/
theorem tsum_lowerNearPerronBound_eq (x : Nat) (T : Real) :
    tsum (lowerNearPerronBound x T) =
      (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
  have hTail : forall n : Nat, Not (Membership.mem (range x) n) ->
      lowerNearPerronBound x T n = 0 := by
    intro n hnMem
    have hnx : Not (n < x) := by
      simpa only [mem_range] using hnMem
    simp [lowerNearPerronBound, hnx]
  rw [tsum_eq_sum hTail]
  calc
    Finset.sum (range x) (lowerNearPerronBound x T) =
        Finset.sum (range x) (fun n : Nat =>
          (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
            (1 / (((x - n : Nat) : Real)))) := by
      apply sum_congr rfl
      intro n hnMem
      have hnx : n < x := mem_range.mp hnMem
      rw [lowerNearPerronBound, if_pos hnx]
      ring
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        Finset.sum (range x) (fun n : Nat =>
          1 / (((x - n : Nat) : Real))) := by
      rw [Finset.mul_sum]
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
      rw [lower_distance_sum_eq_harmonic]

/-- The upper near-range bound sums to the same harmonic factor. -/
theorem tsum_upperNearPerronBound_eq (x : Nat) (T : Real) :
    tsum (upperNearPerronBound x T) =
      (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
  have hTail : forall n : Nat,
      Not (Membership.mem (Ico (x + 1) (2 * x + 1)) n) ->
        upperNearPerronBound x T n = 0 := by
    intro n hnMem
    by_cases hnear : And (x < n) (n <= 2 * x)
    case pos =>
      exfalso
      apply hnMem
      exact mem_Ico.mpr (And.intro
        (Nat.add_one_le_iff.mpr hnear.1) (Nat.lt_succ_iff.mpr hnear.2))
    case neg =>
      simp [upperNearPerronBound, hnear]
  rw [tsum_eq_sum hTail]
  calc
    Finset.sum (Ico (x + 1) (2 * x + 1))
        (upperNearPerronBound x T) =
      Finset.sum (Ico (x + 1) (2 * x + 1)) (fun n : Nat =>
        (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
          (1 / (((n - x : Nat) : Real)))) := by
      apply sum_congr rfl
      intro n hnMem
      have hBounds := mem_Ico.mp hnMem
      have hnear : And (x < n) (n <= 2 * x) := by omega
      rw [upperNearPerronBound, if_pos hnear]
      ring
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        Finset.sum (Ico (x + 1) (2 * x + 1)) (fun n : Nat =>
          1 / (((n - x : Nat) : Real))) := by
      rw [Finset.mul_sum]
    _ = (8 * (x : Real) * Real.log (2 * (x : Real)) / T) *
        (harmonic x : Real) := by
      rw [upper_distance_sum_eq_harmonic]

end BombieriVinogradov.SiegelWalfisz
