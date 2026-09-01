import BombieriVinogradov.Helpers.DirichletCharacter.CpowDerivative
import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumBigO
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Abel derivative majorant for character sums

This module owns the asymptotic estimate for the derivative of the complex
power weight multiplied by a bounded nonprincipal character prefix.
-/

set_option autoImplicit false

open Asymptotics Complex Filter Finset

namespace BombieriVinogradov

/-- The differentiated Abel integrand has the expected `t ^ (-(s + 1).re)` majorant. -/
theorem deriv_cpow_mul_characterPartialSum_isBigO {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) (s : ℂ) :
    (fun t : ℝ => deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, chi k) =O[atTop]
      fun t : ℝ => t ^ (-(s + 1).re) := by
  have hO : (fun n : ℕ => ∑ k ∈ Icc 0 n, chi k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    simpa only [sum_character_Icc_zero_eq_one chi hchi] using
      characterPartialSum_isBigO_rpow_zero chi hchi
  refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) 0 _ ?_ ?_
    (by simp)
  · simpa [-neg_add_rev, neg_add'] using!
      isBigO_deriv_ofReal_cpow_const_atTop (-s)
  · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
      Asymptotics.isEquivalent_nat_floor.isBigO.rpow (show (0 : ℝ) ≤ 0 by rfl)
        (eventually_ge_atTop 0)

end BombieriVinogradov
