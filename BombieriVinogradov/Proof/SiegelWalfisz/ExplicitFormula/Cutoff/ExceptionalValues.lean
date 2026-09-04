import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.UnexcludedValueMembership
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticLFunctionReflection
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith

/-!
# Both exceptional values occur in every positive-height truncation

The selected real zero and its quadratic functional-equation reflection
are ordinary critical-strip zeros of the primitive character.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exceptionalPair_mem_unexcludedCriticalZeroValues
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {c : Real} (hData : ExplicitFormulaZeroFreeData c chi)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi beta)
    {T : Real} (hT : 0 < T) :
    And ((retainedCriticalZeroValues chi T none : Set Complex) beta)
      ((retainedCriticalZeroValues chi T none : Set Complex) (1 - beta)) := by
  have hBetaHeight : abs beta.im < T := by
    simpa [hExceptional.2.1] using hT
  have hBeta := mem_unexcludedCriticalZeroValues_of_LFunction_eq_zero
    hchi hPrimitive hExceptional.2.2.1 hExceptional.2.2.2.1
    hBetaHeight hExceptional.1
  have hReflectPos : 0 < (1 - beta).re := by
    change 0 < 1 - beta.re
    linarith [hExceptional.2.2.2.1]
  have hReflectLt : (1 - beta).re < 1 := by
    change 1 - beta.re < 1
    linarith [hExceptional.2.2.1]
  have hReflectHeight : abs (1 - beta).im < T := by
    simpa [hExceptional.2.1] using hT
  have hFacts := hData.exceptional beta hExceptional
  have hReflectZero : chi.LFunction (1 - beta) = 0 :=
    LFunction_one_sub_eq_zero_of_quadratic hPrimitive hFacts.quadratic
      hExceptional.2.2.1 hExceptional.2.2.2.1 hExceptional.1
  have hReflect := mem_unexcludedCriticalZeroValues_of_LFunction_eq_zero
    hchi hPrimitive hReflectPos hReflectLt hReflectHeight hReflectZero
  exact And.intro hBeta hReflect

end BombieriVinogradov.SiegelWalfisz
