import BombieriVinogradov.Helpers.DirichletCharacter.AbelPowerLocallyIntegrable
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Local integrability of the character Abel kernel

This module owns the floor-indexed character prefix after local integrability
of the smooth complex-power factor has been established.
-/

set_option autoImplicit false

open Finset MeasureTheory Set

namespace BombieriVinogradov

/-- The character Abel kernel is locally integrable on `[1, infinity)`. -/
theorem characterAbelKernel_locallyIntegrableOn {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (s : Complex) :
    LocallyIntegrableOn
      (fun t : Real => (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1)))
      (Ici 1) := by
  have hLocal := locallyIntegrableOn_mul_sum_Icc (fun n : Nat => chi n)
    (a := 1) (m := 1) zero_le_one (locallyIntegrableOn_ofReal_cpow_neg_add_one s)
  simpa only [mul_comm] using hLocal

end BombieriVinogradov
