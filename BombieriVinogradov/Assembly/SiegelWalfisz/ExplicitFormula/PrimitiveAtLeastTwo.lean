import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.PrimitiveAboveTwo
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.PrimitiveAtTwo
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The primitive explicit formula on its full natural endpoint range

The endpoint proof and the contour formula share the same exceptional
constant and are combined without introducing any analytic hypothesis.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitiveExplicitFormula_at_least_two :
    exists c : Real, And (0 < c)
      (And (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        3 <= N -> Ne chi 1 -> ExplicitFormulaZeroFreeData c chi)
      (exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N], 3 <= N ->
          forall {chi : DirichletCharacter Complex N},
            Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 <= x ->
              forall {T : Real}, 2 <= T -> T <= x ->
                forall (exceptional : Option Complex),
                  IsExceptionalZeroChoice c chi exceptional ->
                    norm (characterChebyshevSum x chi +
                      truncatedCriticalZeroSum chi x T exceptional +
                      exceptionalZeroContribution x exceptional) <=
                    C * explicitFormulaRemainderMajorant N x T))) := by
  have hWitness := exists_primitiveExplicitFormula_above_two
  let c : Real := hWitness.choose
  have hc : 0 < c := hWitness.choose_spec.1
  have hData : forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
      3 <= N -> Ne chi 1 -> ExplicitFormulaZeroFreeData c chi :=
    hWitness.choose_spec.2.1
  choose A hA hLarge using hWitness.choose_spec.2.2
  choose E hE hSmall using exists_primitiveExplicitFormula_at_two hc
  refine Exists.intro c (And.intro hc (And.intro hData
    (Exists.intro (A + E) (And.intro (by positivity) ?_))))
  intro N inst hN chi hchi hPrimitive x hx T hT hTx exceptional hChoice
  have hScale : 0 <= explicitFormulaRemainderMajorant N x T := by
    unfold explicitFormulaRemainderMajorant
    have hTPos : 0 < T := by linarith
    positivity
  by_cases hTwo : x = 2
  case pos =>
    subst x
    have hUpper : T <= 2 := by simpa using hTx
    have hEqual : T = 2 := by linarith
    subst T
    have hBound := hSmall hN hchi hPrimitive (hData chi hN hchi)
      exceptional hChoice
    have hCoefficient : E <= A + E := by linarith
    exact hBound.trans (mul_le_mul_of_nonneg_right hCoefficient hScale)
  case neg =>
    have hxGt : 2 < x := by omega
    have hBound := hLarge hN hchi hPrimitive hxGt hT hTx exceptional hChoice
    have hCoefficient : A <= A + E := by linarith
    exact hBound.trans (mul_le_mul_of_nonneg_right hCoefficient hScale)

end BombieriVinogradov.SiegelWalfisz
