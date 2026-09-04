import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ExceptionalPartition
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ExceptionalChoice
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ReflectedContributionBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ZeroSum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Imprimitive comparison of the complete zero contribution

Faithful choices either agree, or the primitive-only exceptional pair
leaves just its reflected contribution after the exact cancellation.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_zeroContribution_sub_primitive_le
    {c : Real} (hc : 0 < c) {N x : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1) (hx : 2 <= x) {T : Real} (hT : 0 < T)
    (hData : ExplicitFormulaZeroFreeData c chi.primitiveCharacter)
    (e ep : Option Complex)
    (hChoice : IsExceptionalZeroChoice c chi e)
    (hPrimitiveChoice : IsExceptionalZeroChoice c chi.primitiveCharacter ep) :
    norm ((truncatedCriticalZeroSum chi x T e + exceptionalZeroContribution x e) -
      (truncatedCriticalZeroSum chi.primitiveCharacter x T ep +
        exceptionalZeroContribution x ep)) <=
      Real.log N / c + (x : Real) ^ (1 / 4 : Real) * Real.log x := by
  have hxPos : 0 < x := by omega
  have hxReal : (2 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hxOne : (1 : Real) <= (x : Real) := by linarith
  have hNonneg : 0 <=
      Real.log N / c + (x : Real) ^ (1 / 4 : Real) * Real.log x := by
    positivity
  have hPrimitiveNe :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  cases e with
  | none =>
    cases ep with
    | none =>
      rw [truncatedCriticalZeroSum_eq_primitive chi hchi hxPos T none]
      simpa using hNonneg
    | some beta =>
      change IsExceptionalZero c chi.primitiveCharacter beta at hPrimitiveChoice
      have hPartition := truncatedCriticalZeroSum_none_eq_exceptionalPartition
        hPrimitiveNe chi.primitiveCharacter_isPrimitive hxPos hData hPrimitiveChoice hT
      have hDifference :
          (truncatedCriticalZeroSum chi x T none + exceptionalZeroContribution x none) -
            (truncatedCriticalZeroSum chi.primitiveCharacter x T (some beta) +
              exceptionalZeroContribution x (some beta)) =
            (x : Complex) ^ (1 - beta) / (1 - beta) := by
        rw [truncatedCriticalZeroSum_eq_primitive chi hchi hxPos T none, hPartition]
        simp only [exceptionalZeroContribution]
        ring
      rw [hDifference]
      have hBound := norm_primitiveExceptional_reflectedContribution_le
        hc chi hchi hData hChoice hPrimitiveChoice hxOne
      simpa only [Complex.ofReal_natCast] using hBound
  | some beta =>
    change IsExceptionalZero c chi beta at hChoice
    have hChoiceEq := primitiveExceptionalChoice_eq_some_of_ambient
      hc chi hchi hData ep hPrimitiveChoice hChoice
    subst ep
    rw [truncatedCriticalZeroSum_eq_primitive chi hchi hxPos T (some beta)]
    simpa using hNonneg

end BombieriVinogradov.SiegelWalfisz
