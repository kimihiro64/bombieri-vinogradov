import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumBigO
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Abel endpoint decay for character sums

This module owns vanishing of the boundary term obtained by multiplying a
bounded nonprincipal character prefix by the decaying weight `n ^ (-s)`.
-/

set_option autoImplicit false

open Asymptotics Filter Finset Topology

namespace BombieriVinogradov

/-- The Abel-summation endpoint term vanishes throughout the half-plane `0 < re s`. -/
theorem characterPartialSum_cpow_tendsto_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ (-s) * ∑ k ∈ Icc 0 n, chi k) atTop (𝓝 0) := by
  have hO : (fun n : ℕ => ∑ k ∈ Icc 0 n, chi k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    simpa only [sum_character_Icc_zero_eq_one chi hchi] using
      characterPartialSum_isBigO_rpow_zero chi hchi
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-s.re)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hlim
  · exact isBigO_norm_left.mp <|
      (Complex.norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
  · linarith

end BombieriVinogradov
