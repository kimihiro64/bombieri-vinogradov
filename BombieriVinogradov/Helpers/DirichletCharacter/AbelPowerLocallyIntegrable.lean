import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Local integrability of the Abel complex-power factor

This module owns local integrability of the smooth complex-power factor on the
positive real ray.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace BombieriVinogradov

/-- The fixed-parameter complex-power factor is locally integrable on `[1, infinity)`. -/
theorem locallyIntegrableOn_ofReal_cpow_neg_add_one (s : Complex) :
    LocallyIntegrableOn (fun t : Real => (t : Complex) ^ (-(s + 1))) (Ici 1) := by
  have hContinuous : ContinuousOn
      (fun t : Real => (t : Complex) ^ (-(s + 1))) (Ici 1) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  exact hContinuous.locallyIntegrableOn measurableSet_Ici

end BombieriVinogradov
