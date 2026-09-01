import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelLocallyIntegrable

/-!
# Measurability of the character Abel kernel

This module owns the measurability consequence of local integrability.
-/

set_option autoImplicit false

open Finset MeasureTheory Set

namespace BombieriVinogradov

/-- The character Abel kernel is strongly almost-everywhere measurable on `(1, infinity)`. -/
theorem characterAbelKernel_aestronglyMeasurable {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (s : Complex) :
    AEStronglyMeasurable
      (fun t : Real => (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1)))
      (volume.restrict (Ioi 1)) := by
  exact ((characterAbelKernel_locallyIntegrableOn chi s).mono_set
    Ioi_subset_Ici_self).aestronglyMeasurable

end BombieriVinogradov
