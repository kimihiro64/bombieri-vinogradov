import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelMeasurable
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Measurability of the character Abel-kernel derivative

This module owns the measurable logarithm factor multiplying the measurable
Abel kernel.
-/

set_option autoImplicit false

open Finset MeasureTheory Set

namespace BombieriVinogradov

/-- The parameter derivative of the Abel kernel is strongly almost-everywhere measurable. -/
theorem characterAbelKernelDerivative_aestronglyMeasurable
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (s : Complex) :
    AEStronglyMeasurable
      (fun t : Real => -((Real.log t : Real) : Complex) *
        ((∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1))))
      (volume.restrict (Ioi 1)) := by
  have hRealLogOn : ContinuousOn (fun t : Real => Real.log t) (Ioi 1) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact Set.mem_compl_singleton_iff.mpr (zero_lt_one.trans ht).ne'
  have hRealLog : AEStronglyMeasurable (fun t : Real => Real.log t)
      (volume.restrict (Ioi 1)) :=
    hRealLogOn.aestronglyMeasurable measurableSet_Ioi
  have hLog : AEStronglyMeasurable
      (fun t : Real => ((Real.log t : Real) : Complex))
      (volume.restrict (Ioi 1)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
  exact hLog.neg.mul (characterAbelKernel_aestronglyMeasurable chi s)

end BombieriVinogradov
