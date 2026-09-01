import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumBound
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Asymptotic form of the character partial-sum bound

This module owns the exponent-zero big-O interfaces consumed by Mathlib's
L-series integral representation.
-/

set_option autoImplicit false

open Asymptotics Filter Finset

namespace BombieriVinogradov

/-- Nonprincipal character partial sums are uniformly bounded at infinity. -/
theorem characterPartialSum_isBigO_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, chi k) =O[atTop] fun _n : ℕ => (1 : ℝ) := by
  refine IsBigO.of_bound (N : ℝ) (Filter.Eventually.of_forall fun n => ?_)
  simpa using norm_sum_character_Icc_le_modulus chi hchi n

/-- The same bound in the exact `n ^ 0` form used by `LSeries_eq_mul_integral`. -/
theorem characterPartialSum_isBigO_rpow_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, chi k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
  simpa using characterPartialSum_isBigO_one chi hchi

end BombieriVinogradov
