import BombieriVinogradov.Helpers.DirichletCharacter.AbelDerivativeMajorant
import BombieriVinogradov.Helpers.DirichletCharacter.AbelDerivativeMajorantIntegrable
import BombieriVinogradov.Helpers.DirichletCharacter.AbelDerivativeMeasurable
import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelDerivative
import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelIntegrable
import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelMeasurable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Differentiation under the character Abel-kernel integral

This module owns the dominated parametric-integral application after all
measurability, integrability, pointwise derivative, and majorant inputs have
been isolated.
-/

set_option autoImplicit false

open Filter Finset MeasureTheory Set Topology

namespace BombieriVinogradov

/-- The character Abel-kernel integral can be differentiated under its integral sign. -/
theorem characterAbelKernelIntegral_hasDerivAt {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1)
    {s0 : Complex} (hs0 : 0 < s0.re) :
    HasDerivAt
      (fun z : Complex => ∫ t in Ioi (1 : Real),
        (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(z + 1)))
      (∫ t in Ioi (1 : Real), -((Real.log t : Real) : Complex) *
        ((∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s0 + 1)))) s0 := by
  let F : Complex → Real → Complex := fun z t =>
    (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(z + 1))
  let F' : Complex → Real → Complex := fun z t =>
    -((Real.log t : Real) : Complex) *
      ((∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(z + 1)))
  let bound : Real → Real := fun t =>
    (N : Real) * (Real.log t * t ^ (-(s0.re / 2 + 1)))
  have hNeighborhood : Metric.ball s0 (s0.re / 2) ∈ 𝓝 s0 :=
    Metric.ball_mem_nhds s0 (half_pos hs0)
  have hFMeasurable : ∀ᶠ z in 𝓝 s0,
      AEStronglyMeasurable (F z) (volume.restrict (Ioi (1 : Real))) := by
    exact Eventually.of_forall fun z => characterAbelKernel_aestronglyMeasurable chi z
  have hFIntegrable : Integrable (F s0) (volume.restrict (Ioi (1 : Real))) := by
    exact characterAbelKernel_integrableOn chi hchi hs0
  have hF'DerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioi (1 : Real))) := by
    exact characterAbelKernelDerivative_aestronglyMeasurable chi s0
  have hBound : ∀ᵐ t ∂volume.restrict (Ioi (1 : Real)),
      ∀ z ∈ Metric.ball s0 (s0.re / 2), ‖F' z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    exact norm_characterAbelKernelDerivative_le chi hchi hz (mem_Ioi.mp ht)
  have hBoundIntegrable : Integrable bound (volume.restrict (Ioi (1 : Real))) := by
    exact integrableOn_characterAbelDerivativeMajorant (N := N) hs0
  have hDerivative : ∀ᵐ t ∂volume.restrict (Ioi (1 : Real)),
      ∀ z ∈ Metric.ball s0 (s0.re / 2), HasDerivAt (fun w : Complex => F w t) (F' z t) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z _hz
    exact characterAbelKernel_hasDerivAt chi (mem_Ioi.mp ht) z
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) hNeighborhood hFMeasurable
    hFIntegrable hF'DerivativeMeasurable hBound hBoundIntegrable hDerivative
  simpa [F, F', bound] using hMain.2

end BombieriVinogradov
