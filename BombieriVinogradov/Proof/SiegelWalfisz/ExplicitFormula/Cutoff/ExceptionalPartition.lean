import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ExceptionalValuePartition
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedCriticalZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedExceptionalDisjoint
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Exact change of the zero sum after excluding the exceptional pair

Residues retain analytic multiplicities. Simplicity of the selected zero
and its quadratic reflection evaluates the two excluded contributions.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedCriticalZeroSum_none_eq_exceptionalPartition
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hx : 0 < x) {c : Real} (hData : ExplicitFormulaZeroFreeData c chi)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi beta)
    {T : Real} (hT : 0 < T) :
    truncatedCriticalZeroSum chi x T none =
      truncatedCriticalZeroSum chi x T (some beta) +
        (x : Complex) ^ beta / beta +
        (x : Complex) ^ (1 - beta) / (1 - beta) := by
  have hValues := unexcludedCriticalZeroValues_eq_exceptionalPartition
    hchi hPrimitive hData hExceptional hT
  have hDisjoint := disjoint_retainedCriticalZeroValues_exceptionalZeroValues
    chi T (some beta)
  have hSums :
      Finset.sum (retainedCriticalZeroValues chi T none)
          (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) =
        Finset.sum (retainedCriticalZeroValues chi T (some beta))
          (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) +
        Finset.sum (exceptionalZeroValues (some beta))
          (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) := by
    rw [hValues, Finset.sum_union hDisjoint]
  have hFacts := hData.exceptional beta hExceptional
  rw [sum_residue_regularizedExplicitFormulaIntegrand_retainedCriticalZeroValues
      hchi hx T none,
    sum_residue_regularizedExplicitFormulaIntegrand_retainedCriticalZeroValues
      hchi hx T (some beta),
    sum_residue_regularizedExplicitFormulaIntegrand_exceptionalZeroValues_some
      hchi hPrimitive hFacts.quadratic hx hExceptional
        hFacts.simple hFacts.reflection_ne] at hSums
  calc
    truncatedCriticalZeroSum chi x T none =
        -(-truncatedCriticalZeroSum chi x T none) := (neg_neg _).symm
    _ = -(-truncatedCriticalZeroSum chi x T (some beta) +
        (-((x : Complex) ^ beta / beta) +
          -((x : Complex) ^ (1 - beta) / (1 - beta)))) := by
      rw [hSums]
    _ = truncatedCriticalZeroSum chi x T (some beta) +
        (x : Complex) ^ beta / beta +
        (x : Complex) ^ (1 - beta) / (1 - beta) := by
      ring

end BombieriVinogradov.SiegelWalfisz
