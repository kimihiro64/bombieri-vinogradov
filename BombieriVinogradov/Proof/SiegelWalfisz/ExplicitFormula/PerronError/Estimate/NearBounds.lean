import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions

/-!
# Finite-support central-range bounds

This module defines the lower and upper harmonic kernels used to dominate the
two central Perron ranges and proves their finite-support summability.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace BombieriVinogradov.SiegelWalfisz

/-- The harmonic distance bound for indices below `x`. -/
def lowerNearPerronBound (x : Nat) (T : Real) (n : Nat) : Real :=
  if n < x then
    8 * (x : Real) * Real.log (2 * (x : Real)) /
      (T * ((x - n : Nat) : Real))
  else 0

/-- The harmonic distance bound for indices above `x` through `2 * x`. -/
def upperNearPerronBound (x : Nat) (T : Real) (n : Nat) : Real :=
  if And (x < n) (n <= 2 * x) then
    8 * (x : Real) * Real.log (2 * (x : Real)) /
      (T * ((n - x : Nat) : Real))
  else 0

/-- The lower harmonic kernel is nonnegative for positive `x` and `T`. -/
theorem lowerNearPerronBound_nonneg
    {x : Nat} (hx : 0 < x) {T : Real} (hT : 0 < T) (n : Nat) :
    0 <= lowerNearPerronBound x T n := by
  unfold lowerNearPerronBound
  split
  case isTrue hnx =>
    have hDist : 0 < ((x - n : Nat) : Real) := by
      exact_mod_cast Nat.sub_pos_of_lt hnx
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    have hLog : 0 <= Real.log (2 * (x : Real)) := by
      apply Real.log_nonneg
      nlinarith [hxOne]
    positivity
  case isFalse =>
    exact le_refl 0

/-- The upper harmonic kernel is nonnegative for positive `x` and `T`. -/
theorem upperNearPerronBound_nonneg
    {x : Nat} (hx : 0 < x) {T : Real} (hT : 0 < T) (n : Nat) :
    0 <= upperNearPerronBound x T n := by
  unfold upperNearPerronBound
  split
  case isTrue hnear =>
    have hDist : 0 < ((n - x : Nat) : Real) := by
      exact_mod_cast Nat.sub_pos_of_lt hnear.1
    have hxOne : (1 : Real) <= (x : Real) := by exact_mod_cast hx
    have hLog : 0 <= Real.log (2 * (x : Real)) := by
      apply Real.log_nonneg
      nlinarith [hxOne]
    positivity
  case isFalse =>
    exact le_refl 0

/-- The lower harmonic kernel has finite support. -/
theorem summable_lowerNearPerronBound (x : Nat) (T : Real) :
    Summable (lowerNearPerronBound x T) := by
  apply summable_of_ne_finset_zero (s := range x)
  intro n hnMem
  have hnx : Not (n < x) := by
    simpa only [mem_range] using hnMem
  simp [lowerNearPerronBound, hnx]

/-- The upper harmonic kernel has finite support. -/
theorem summable_upperNearPerronBound (x : Nat) (T : Real) :
    Summable (upperNearPerronBound x T) := by
  apply summable_of_ne_finset_zero (s := Ico (x + 1) (2 * x + 1))
  intro n hnMem
  by_cases hnear : And (x < n) (n <= 2 * x)
  case pos =>
    exfalso
    apply hnMem
    exact mem_Ico.mpr (And.intro
      (Nat.add_one_le_iff.mpr hnear.1) (Nat.lt_succ_iff.mpr hnear.2))
  case neg =>
    simp [upperNearPerronBound, hnear]

end BombieriVinogradov.SiegelWalfisz
