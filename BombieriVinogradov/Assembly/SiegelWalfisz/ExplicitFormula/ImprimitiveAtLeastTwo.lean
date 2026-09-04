import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.ImprimitiveZeroContribution
import BombieriVinogradov.Helpers.ComplexAnalysis.ReferenceSumComparison
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ChebyshevCorrection
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.ImprimitiveError
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.LevelMonotonicity
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Transfer of a primitive explicit-formula bound

The reference residual, finite Euler correction and complete zero-contribution
correction are bounded separately, then combined on the ambient source scale.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem explicitFormula_of_primitive_bound
    {c C : Real} (hc : 0 < c) (hC : 0 <= C) {N x : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1) (hx : 2 <= x) {T : Real} (hT : 2 <= T) (hTx : T <= x)
    (hData : ExplicitFormulaZeroFreeData c chi.primitiveCharacter)
    (e ep : Option Complex) (hChoice : IsExceptionalZeroChoice c chi e)
    (hPrimitiveChoice : IsExceptionalZeroChoice c chi.primitiveCharacter ep)
    (hPrimitive : norm (characterChebyshevSum x chi.primitiveCharacter +
      truncatedCriticalZeroSum chi.primitiveCharacter x T ep +
        exceptionalZeroContribution x ep) <=
      C * explicitFormulaRemainderMajorant chi.conductor x T) :
    norm (characterChebyshevSum x chi + truncatedCriticalZeroSum chi x T e +
      exceptionalZeroContribution x e) <=
      (C + (1 / Real.log (2 : Real) + 1 / c + 1)) *
        explicitFormulaRemainderMajorant N x T := by
  have hN := DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hd := DirichletCharacter.three_le_conductor_of_ne_one chi hchi
  have hLevel := explicitFormulaRemainderMajorant_mono_level
    hd (DirichletCharacter.conductor_le_level chi) hx hT
  have hPrimitiveAmbient :=
    hPrimitive.trans (mul_le_mul_of_nonneg_left hLevel hC)
  have hxPos : 0 < x := by omega
  have hTPos : 0 < T := by linarith
  have hEuler := norm_characterChebyshevSum_sub_primitive_le (NeZero.ne N) chi hxPos
  have hZeros := norm_zeroContribution_sub_primitive_le
    hc chi hchi hx hTPos hData e ep hChoice hPrimitiveChoice
  have hTriangle :
      norm (characterChebyshevSum x chi + truncatedCriticalZeroSum chi x T e +
        exceptionalZeroContribution x e) <=
      norm (characterChebyshevSum x chi.primitiveCharacter +
        truncatedCriticalZeroSum chi.primitiveCharacter x T ep +
          exceptionalZeroContribution x ep) +
      norm (characterChebyshevSum x chi - characterChebyshevSum x chi.primitiveCharacter) +
      norm ((truncatedCriticalZeroSum chi x T e + exceptionalZeroContribution x e) -
        (truncatedCriticalZeroSum chi.primitiveCharacter x T ep +
          exceptionalZeroContribution x ep)) := by
    simpa only [add_assoc] using ComplexAnalysis.norm_sum_le_reference_and_differences
      (characterChebyshevSum x chi)
      (truncatedCriticalZeroSum chi x T e + exceptionalZeroContribution x e)
      (characterChebyshevSum x chi.primitiveCharacter)
      (truncatedCriticalZeroSum chi.primitiveCharacter x T ep +
        exceptionalZeroContribution x ep)
  have hError := imprimitive_correction_le_remainder hc hN hx hT hTx
  calc
    norm (characterChebyshevSum x chi + truncatedCriticalZeroSum chi x T e +
        exceptionalZeroContribution x e) <=
        C * explicitFormulaRemainderMajorant N x T +
          (Real.log N * Real.log x / Real.log (2 : Real) + Real.log N / c +
            (x : Real) ^ (1 / 4 : Real) * Real.log x) := by linarith
    _ <= C * explicitFormulaRemainderMajorant N x T +
        (1 / Real.log (2 : Real) + 1 / c + 1) *
          explicitFormulaRemainderMajorant N x T := by linarith
    _ = (C + (1 / Real.log (2 : Real) + 1 / c + 1)) *
        explicitFormulaRemainderMajorant N x T := by ring

end BombieriVinogradov.SiegelWalfisz
