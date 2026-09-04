import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalZeroResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedValueGeometry
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.RetainedValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ZeroResidue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionOrder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# The fixed-choice zero sum is invariant under primitive induction

The retained complex values and the ordinary L-function multiplicities
agree. Comparing the finite residue sums preserves every term and its
multiplicity without identifying zeros outside the strict critical strip.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedCriticalZeroSum_eq_primitive
    {N x : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Ne chi 1) (hx : 0 < x)
    (T : Real) (exceptional : Option Complex) :
    truncatedCriticalZeroSum chi x T exceptional =
      truncatedCriticalZeroSum chi.primitiveCharacter x T exceptional := by
  have hPrimitiveNe : Ne chi.primitiveCharacter 1 :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi
  have hValues := retainedCriticalZeroValues_eq_primitive chi hchi T exceptional
  have hSums :
      Finset.sum (retainedCriticalZeroValues chi T exceptional)
        (fun rho => residue (explicitFormulaIntegrand chi x) rho) =
      Finset.sum (retainedCriticalZeroValues chi.primitiveCharacter T exceptional)
        (fun rho => residue (explicitFormulaIntegrand chi.primitiveCharacter x) rho) := by
    rw [hValues]
    apply Finset.sum_congr rfl
    intro rho hrho
    have hNonzero : Ne rho 0 := ne_zero_of_mem_retainedCriticalZeroValues hrho
    have hRe : 0 < rho.re := (retainedCriticalZeroValue_mem_strip hrho).1
    rw [residue_explicitFormulaIntegrand hchi hx hNonzero,
      residue_explicitFormulaIntegrand hPrimitiveNe hx hNonzero,
      analyticOrderNatAt_LFunction_eq_primitive chi hchi hRe]
  have hChiSum := sum_residue_explicitFormulaIntegrand_retainedCriticalZeroValues
    hchi hx T exceptional
  have hPrimitiveSum :=
    sum_residue_explicitFormulaIntegrand_retainedCriticalZeroValues
      hPrimitiveNe hx T exceptional
  rw [hChiSum, hPrimitiveSum] at hSums
  simpa only [neg_neg] using congrArg (fun z : Complex => -z) hSums

end BombieriVinogradov.SiegelWalfisz
