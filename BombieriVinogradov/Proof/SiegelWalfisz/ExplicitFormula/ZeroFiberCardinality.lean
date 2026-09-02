import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalStripZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLFunctionOrder
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-!
# Multiplicity of a retained zero value

This module identifies the retained divisor-index fiber over one critical-strip
value with that value's ordinary Dirichlet L-function analytic multiplicity.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem retainedCriticalZeroFiber_card_eq_analyticOrderNatAt
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) {T : Real} {exceptional : Option Complex}
    {rho : Complex} (hrho : rho ∈ retainedCriticalZeroValues chi T exceptional) :
    ((retainedCriticalZeroIndices chi T exceptional).filter fun p =>
        Complex.Hadamard.divisorZeroIndex₀_val p = rho).card =
      analyticOrderNatAt chi.LFunction rho := by
  classical
  have hWitness := Finset.mem_image.mp hrho
  let p := hWitness.choose
  have hp : p ∈ retainedCriticalZeroIndices chi T exceptional :=
    hWitness.choose_spec.1
  have hpValue : Complex.Hadamard.divisorZeroIndex₀_val p = rho :=
    hWitness.choose_spec.2
  have hpData := mem_retainedCriticalZeroIndices_iff.mp hp
  have hrhoStrip :
      0 < rho.re ∧ rho.re < 1 ∧ |rho.im| < T := by
    simpa [hpValue] using
      (mem_criticalStripZeroTruncation_iff.mp hpData.1)
  have hrhoRetained : IsRetainedZero exceptional rho := by
    simpa [hpValue] using hpData.2
  have hrhoNe := ne_zero_of_mem_retainedCriticalZeroValues hrho
  have hFiber :
      (retainedCriticalZeroIndices chi T exceptional).filter (fun q =>
          Complex.Hadamard.divisorZeroIndex₀_val q = rho) =
        Complex.Hadamard.divisorZeroIndex₀_fiberFinset
          (symmetricCompletedLFunction chi) rho := by
    apply Finset.ext
    intro q
    rw [Finset.mem_filter, mem_retainedCriticalZeroIndices_iff,
      Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset]
    constructor
    · intro hq
      exact hq.2
    · intro hqValue
      have hqTruncated : q ∈ criticalStripZeroTruncation chi T := by
        rw [mem_criticalStripZeroTruncation_iff, hqValue]
        exact hrhoStrip
      have hqRetained :
          IsRetainedZero exceptional
            (Complex.Hadamard.divisorZeroIndex₀_val q) := by
        simpa [hqValue] using hrhoRetained
      exact And.intro (And.intro hqTruncated hqRetained) hqValue
  rw [hFiber]
  calc
    (Complex.Hadamard.divisorZeroIndex₀_fiberFinset
        (symmetricCompletedLFunction chi) rho).card =
        analyticOrderNatAt (symmetricCompletedLFunction chi) rho :=
      Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
        (differentiable_symmetricCompletedLFunction hchi) hrhoNe
    _ = analyticOrderNatAt chi.LFunction rho :=
      analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi hrhoStrip.1

end BombieriVinogradov.SiegelWalfisz
