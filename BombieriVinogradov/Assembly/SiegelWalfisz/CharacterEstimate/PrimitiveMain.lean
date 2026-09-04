import BombieriVinogradov.Assembly.SiegelWalfisz.CharacterEstimate.PrimitiveSelectedZeroSum
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.Main
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Helpers.RealAnalysis.SmallDecayRate
import BombieriVinogradov.Helpers.RealAnalysis.SqrtLogHeight
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.SelectedRemainder
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The uniform primitive exceptional character estimate

The same zero-free constant governs the formula and retained zeros.
All constants are chosen before the modulus, character and endpoint.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem primitiveCharacterChebyshevExceptional :
    exists c a C : Real, And (0 < c)
      (And (0 < a) (And (a <= (1 / 2 : Real)) (And (2 * a <= c / 4)
        (And (0 < C)
          (And (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
            Ne chi 1 -> ExplicitFormulaZeroFreeData c chi)
          (forall {N : Nat} [NeZero N] {chi : _root_.DirichletCharacter Complex N},
            Ne chi 1 -> _root_.DirichletCharacter.IsPrimitive chi ->
              forall {x : Nat}, 3 <= x ->
                (N : Real) <= Real.exp (Real.sqrt (Real.log x)) ->
                  forall (e : Option Complex), IsExceptionalZeroChoice c chi e ->
                    norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) <=
                      C * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))))))))) := by
  classical
  have hWitness := dirichletExplicitFormula
  let c : Real := hWitness.choose
  have hc : 0 < c := hWitness.choose_spec.1
  have hData : forall {N : Nat} [NeZero N]
      (chi : _root_.DirichletCharacter Complex N),
      Ne chi 1 -> ExplicitFormulaZeroFreeData c chi := hWitness.choose_spec.2.1
  choose C0 hC0 hFormula using hWitness.choose_spec.2.2
  choose a ha hRate using BombieriVinogradov.RealAnalysis.exists_positive_small_decay_rate hc
  choose K hK hZero using
    exists_norm_truncatedCriticalZeroSum_selectedHeight_le_exp hc ha hRate.2
  refine Exists.intro c (Exists.intro a (Exists.intro (1568 * C0 + K) ?_))
  refine And.intro hc (And.intro ha (And.intro hRate.1 (And.intro hRate.2 ?_)))
  refine And.intro (by positivity) (And.intro hData ?_)
  intro N inst chi hchi hPrimitive x hx hModulus e hChoice
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hxTwo : 2 <= x := by omega
  have hxReal : (3 : Real) <= (x : Real) := Nat.cast_le.mpr hx
  have hGeometry := BombieriVinogradov.RealAnalysis.sqrtLog_height_bounds hxReal
  let F : Real := (x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))
  change norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) <=
    (1568 * C0 + K) * F
  have hExplicit := hFormula hchi hxTwo hGeometry.2.2.1 hGeometry.2.2.2 e hChoice
  have hRemainder :
      explicitFormulaRemainderMajorant N x (Real.exp (Real.sqrt (Real.log x))) <=
        1568 * F := by
    simpa only [F] using
      explicitFormulaRemainderMajorant_selectedHeight_le_exp hRate.1 hN hx hModulus
  have hResidual := hExplicit.trans (mul_le_mul_of_nonneg_left hRemainder hC0.le)
  have hZeroBound :
      norm (truncatedCriticalZeroSum chi x (Real.exp (Real.sqrt (Real.log x))) e) <=
        K * F := by
    simpa only [F] using hZero hN hchi hPrimitive (hData chi hchi) e hChoice hx hModulus
  have hTriangle :
      norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) <=
        norm (characterChebyshevSum x chi +
          truncatedCriticalZeroSum chi x (Real.exp (Real.sqrt (Real.log x))) e +
          exceptionalZeroContribution x e) +
        norm (truncatedCriticalZeroSum chi x (Real.exp (Real.sqrt (Real.log x))) e) := by
    have hIdentity : characterChebyshevSum x chi + exceptionalZeroContribution x e =
        (characterChebyshevSum x chi +
          truncatedCriticalZeroSum chi x (Real.exp (Real.sqrt (Real.log x))) e +
          exceptionalZeroContribution x e) -
            truncatedCriticalZeroSum chi x (Real.exp (Real.sqrt (Real.log x))) e := by ring
    rw [hIdentity]
    exact norm_sub_le _ _
  linarith only [hTriangle, hResidual, hZeroBound]

end BombieriVinogradov.SiegelWalfisz
