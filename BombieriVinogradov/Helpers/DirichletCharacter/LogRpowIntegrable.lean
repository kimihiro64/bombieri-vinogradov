import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Integrability of a logarithmic power majorant

This module owns the tail integrability estimate needed when differentiating
the character Abel integral with respect to its complex parameter.
-/

set_option autoImplicit false

open Asymptotics Filter MeasureTheory Set

namespace BombieriVinogradov

/-- `log t * t ^ (-sigma - 1)` is integrable on `(1, infinity)` when `sigma` is positive. -/
theorem integrableOn_log_mul_rpow_neg_add_one {sigma : Real} (hsigma : 0 < sigma) :
    IntegrableOn (fun t : Real => Real.log t * t ^ (-(sigma + 1))) (Ioi 1) := by
  have hsigmaHalf : 0 < sigma / 2 := half_pos hsigma
  have hLog : Real.log =O[atTop] fun t : Real => t ^ (sigma / 2) :=
    (isLittleO_log_rpow_atTop hsigmaHalf).isBigO
  have hPower : (fun t : Real => t ^ (-(sigma + 1))) =O[atTop]
      fun t : Real => t ^ (-(sigma + 1)) :=
    isBigO_refl _ _
  have hMajorant : (fun t : Real => Real.log t * t ^ (-(sigma + 1))) =O[atTop]
      fun t : Real => t ^ (-(sigma / 2 + 1)) := by
    simpa using!
      IsBigO.mul_atTop_rpow_of_isBigO_rpow (sigma / 2) (-(sigma + 1))
        (-(sigma / 2 + 1)) hLog hPower (by linarith)
  have hIntegrable : IntegrableAtFilter (fun t : Real => t ^ (-(sigma / 2 + 1))) atTop := by
    rw [integrableAtFilter_rpow_atTop_iff]
    linarith
  have hContinuous : ContinuousOn
      (fun t : Real => Real.log t * t ^ (-(sigma + 1))) (Ici 1) := by
    intro t ht
    have htPos : 0 < t := zero_lt_one.trans_le ht
    exact ((Real.continuousAt_log htPos.ne').mul
      (Real.continuousAt_rpow_const _ _ (Or.inl htPos.ne'))).continuousWithinAt
  have hIntegrableIci :=
    (hContinuous.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
      hMajorant hIntegrable
  exact hIntegrableIci.mono_set Ioi_subset_Ici_self

end BombieriVinogradov
