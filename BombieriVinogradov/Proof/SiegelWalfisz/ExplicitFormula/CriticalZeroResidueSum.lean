import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ZeroFiberCardinality
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ZeroResidue

/-!
# Finite sum of critical-zero residues

This module groups retained divisor indices by their complex value and converts
the resulting multiplicities into the residue sum for the source integrand.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_residue_explicitFormulaIntegrand_retainedCriticalZeroValues
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hx : 0 < x) (T : Real)
    (exceptional : Option Complex) :
    ∑ rho ∈ retainedCriticalZeroValues chi T exceptional,
        residue (explicitFormulaIntegrand chi x) rho =
      -truncatedCriticalZeroSum chi x T exceptional := by
  classical
  let indices := retainedCriticalZeroIndices chi T exceptional
  let values := retainedCriticalZeroValues chi T exceptional
  let zeroTerm : Complex -> Complex := fun rho => (x : Complex) ^ rho / rho
  have hMaps : forall p, p ∈ indices ->
      Complex.Hadamard.divisorZeroIndex₀_val p ∈ values := by
    intro p hp
    exact Finset.mem_image.mpr (Exists.intro p (And.intro hp rfl))
  have hFiberTerm : forall rho, rho ∈ values ->
      ∑ p ∈ indices with Complex.Hadamard.divisorZeroIndex₀_val p = rho,
          zeroTerm (Complex.Hadamard.divisorZeroIndex₀_val p) =
        (analyticOrderNatAt chi.LFunction rho : Complex) * zeroTerm rho := by
    intro rho hrho
    calc
      (∑ p ∈ indices with Complex.Hadamard.divisorZeroIndex₀_val p = rho,
          zeroTerm (Complex.Hadamard.divisorZeroIndex₀_val p)) =
          ∑ _p ∈ indices.filter (fun p =>
              Complex.Hadamard.divisorZeroIndex₀_val p = rho),
            zeroTerm rho := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpValue := (Finset.mem_filter.mp hp).2
        rw [hpValue]
      _ = ((indices.filter fun p =>
              Complex.Hadamard.divisorZeroIndex₀_val p = rho).card : Complex) *
            zeroTerm rho := by
        simp
      _ = (analyticOrderNatAt chi.LFunction rho : Complex) * zeroTerm rho := by
        rw [retainedCriticalZeroFiber_card_eq_analyticOrderNatAt hchi]
        exact hrho
  have hGrouped :
      ∑ rho ∈ values,
          (analyticOrderNatAt chi.LFunction rho : Complex) * zeroTerm rho =
        ∑ p ∈ indices, zeroTerm (Complex.Hadamard.divisorZeroIndex₀_val p) := by
    calc
      (∑ rho ∈ values,
          (analyticOrderNatAt chi.LFunction rho : Complex) * zeroTerm rho) =
          ∑ rho ∈ values,
            ∑ p ∈ indices with Complex.Hadamard.divisorZeroIndex₀_val p = rho,
              zeroTerm (Complex.Hadamard.divisorZeroIndex₀_val p) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        exact (hFiberTerm rho hrho).symm
      _ = ∑ p ∈ indices,
          zeroTerm (Complex.Hadamard.divisorZeroIndex₀_val p) :=
        Finset.sum_fiberwise_of_maps_to hMaps
          (fun p => zeroTerm (Complex.Hadamard.divisorZeroIndex₀_val p))
  change ∑ rho ∈ values, residue (explicitFormulaIntegrand chi x) rho = _
  calc
    (∑ rho ∈ values, residue (explicitFormulaIntegrand chi x) rho) =
        ∑ rho ∈ values,
          -((analyticOrderNatAt chi.LFunction rho : Nat) : Complex) *
            zeroTerm rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      simpa [zeroTerm] using
        residue_explicitFormulaIntegrand hchi hx
          (ne_zero_of_mem_retainedCriticalZeroValues hrho)
    _ = -(∑ rho ∈ values,
          (analyticOrderNatAt chi.LFunction rho : Complex) * zeroTerm rho) := by
      simp
    _ = -(∑ p ∈ indices,
          zeroTerm (Complex.Hadamard.divisorZeroIndex₀_val p)) := by
      rw [hGrouped]
    _ = -truncatedCriticalZeroSum chi x T exceptional := by
      rw [truncatedCriticalZeroSum_eq_sum_retainedCriticalZeroIndices]

end BombieriVinogradov.SiegelWalfisz
