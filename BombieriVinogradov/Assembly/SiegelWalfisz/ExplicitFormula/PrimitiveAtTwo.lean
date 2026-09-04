import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.EndpointZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Endpoint.ChebyshevSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Endpoint.ExceptionalTerm
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.EndpointTwo
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The primitive explicit formula at x=T=2

The finite sum, retained zero sum and optional exceptional term are
bounded directly. The constant is chosen before all character data.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitiveExplicitFormula_at_two {c : Real} (hc : 0 < c) :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
          ExplicitFormulaZeroFreeData c chi ->
          forall (exceptional : Option Complex),
            IsExceptionalZeroChoice c chi exceptional ->
              norm (characterChebyshevSum 2 chi +
                truncatedCriticalZeroSum chi 2 2 exceptional +
                exceptionalZeroContribution 2 exceptional) <=
              C * explicitFormulaRemainderMajorant N 2 2) := by
  choose A hA hZero using
    exists_norm_truncatedCriticalZeroSum_two_le_sourceScale hc
  refine Exists.intro (A + 4) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive hData exceptional hChoice
  let P := (Real.log ((N * 2 : Nat) : Real)) ^ 2
  have hP : 1 <= P := (endpointTwo_sourceLog_bounds hN).1
  have hLogTwo : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : Real)) (by norm_num)
    linarith
  have hPsi := (norm_characterChebyshevSum_two_le_log_two chi).trans hLogTwo
  have hZeroBound : norm (truncatedCriticalZeroSum chi 2 2 exceptional) <=
      A * P := by
    simpa only [P] using hZero hN hchi hPrimitive hData exceptional hChoice
  have hExceptional := norm_exceptionalZeroContribution_two_le hData
    exceptional hChoice
  have hTotal := norm_add_le_of_le
    (norm_add_le_of_le hPsi hZeroBound) hExceptional
  have hAbsorb : 1 + A * P + 8 / 3 <= (A + 4) * P := by nlinarith
  have hQ : 0 <= (2 : Real) ^ (1 / 4 : Real) * Real.log 2 := by positivity
  have hScaleEq : explicitFormulaRemainderMajorant N 2 2 =
      P + (2 : Real) ^ (1 / 4 : Real) * Real.log 2 := by
    norm_num [explicitFormulaRemainderMajorant, P]
  have hScale : P <= explicitFormulaRemainderMajorant N 2 2 := by
    rw [hScaleEq]
    linarith
  exact hTotal.trans (hAbsorb.trans
    (mul_le_mul_of_nonneg_left hScale (by positivity)))

end BombieriVinogradov.SiegelWalfisz
