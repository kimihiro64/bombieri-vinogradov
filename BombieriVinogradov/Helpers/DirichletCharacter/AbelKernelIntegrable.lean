import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelLocallyIntegrable
import BombieriVinogradov.Helpers.DirichletCharacter.CpowMajorantIntegrable
import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Global integrability of the character Abel kernel

This module owns the combination of local integrability with the bounded
character-prefix tail estimate on the positive-real-part half-plane.
-/

set_option autoImplicit false

open Asymptotics Filter Finset MeasureTheory Set

namespace BombieriVinogradov

/-- The nonprincipal character Abel kernel is integrable when `re(s)>0`. -/
theorem characterAbelKernel_integrableOn {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1)
    {s : Complex} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : Real => (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1)))
      (Ioi 1) := by
  have hMajorant :
      (fun t : Real => (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1))) =O[atTop]
        fun t : Real => t ^ (-(s + 1).re) := by
    refine IsBigO.of_bound (N : Real) ?_
    filter_upwards [eventually_gt_atTop (1 : Real)] with t ht
    have htPos : 0 < t := zero_lt_one.trans ht
    have hPowerNonneg : 0 ≤ t ^ (-(s + 1).re) := Real.rpow_nonneg htPos.le _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htPos,
      Real.norm_of_nonneg hPowerNonneg]
    exact mul_le_mul_of_nonneg_right
      (norm_sum_character_Icc_le_modulus chi hchi ⌊t⌋₊) hPowerNonneg
  have hIntegrableIci :=
    (characterAbelKernel_locallyIntegrableOn chi s).integrableOn_of_isBigO_atTop
      hMajorant (integrableAtFilter_rpow_neg_add_one_re hs)
  exact hIntegrableIci.mono_set Ioi_subset_Ici_self

end BombieriVinogradov
