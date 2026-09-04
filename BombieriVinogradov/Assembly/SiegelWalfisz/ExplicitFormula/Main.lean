import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.ImprimitiveAtLeastTwo
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.PrimitiveAtLeastTwo
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.FaithfulChoice
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The uniform truncated Dirichlet explicit formula

The primitive formula and the complete imprimitive transfer use the same
absolute zero-free constant. One error constant works for every level,
nonprincipal character, admissible endpoint and height, and faithful choice.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem dirichletExplicitFormula :
    exists c : Real, And (0 < c)
      (And (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
        Ne chi 1 -> ExplicitFormulaZeroFreeData c chi)
      (exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N] {chi : _root_.DirichletCharacter Complex N},
          Ne chi 1 -> forall {x : Nat}, 2 <= x ->
            forall {T : Real}, 2 <= T -> T <= x ->
              forall (e : Option Complex), IsExceptionalZeroChoice c chi e ->
                norm (characterChebyshevSum x chi + truncatedCriticalZeroSum chi x T e +
                  exceptionalZeroContribution x e) <=
                    C * explicitFormulaRemainderMajorant N x T))) := by
  classical
  have hWitness := exists_primitiveExplicitFormula_at_least_two
  let c : Real := hWitness.choose
  have hc : 0 < c := hWitness.choose_spec.1
  have hData : forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
      3 <= N -> Ne chi 1 -> ExplicitFormulaZeroFreeData c chi :=
    hWitness.choose_spec.2.1
  have hGlobalData : forall {N : Nat} [NeZero N]
      (chi : _root_.DirichletCharacter Complex N),
      Ne chi 1 -> ExplicitFormulaZeroFreeData c chi := by
    intro N inst chi hchi
    exact hData chi (DirichletCharacter.three_le_level_of_ne_one chi hchi) hchi
  choose C hC hPrimitive using hWitness.choose_spec.2.2
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hNewPos : 0 < C + (1 / Real.log (2 : Real) + 1 / c + 1) := by positivity
  refine Exists.intro c (And.intro hc (And.intro hGlobalData
    (Exists.intro (C + (1 / Real.log (2 : Real) + 1 / c + 1)) (And.intro hNewPos ?_))))
  intro N inst chi hchi x hx T hT hTx e hChoice
  let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  have hd := DirichletCharacter.three_le_conductor_of_ne_one chi hchi
  have hPrimitiveNe := DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hChoiceExists := exists_faithfulExceptionalChoice c chi.primitiveCharacter
  let ep : Option Complex := hChoiceExists.choose
  have hEp : IsExceptionalZeroChoice c chi.primitiveCharacter ep := hChoiceExists.choose_spec
  have hBound := hPrimitive hd hPrimitiveNe chi.primitiveCharacter_isPrimitive
    hx hT hTx ep hEp
  exact explicitFormula_of_primitive_bound hc hC.le chi hchi hx hT hTx
    (hGlobalData chi.primitiveCharacter hPrimitiveNe) e ep hChoice hEp hBound

end BombieriVinogradov.SiegelWalfisz
