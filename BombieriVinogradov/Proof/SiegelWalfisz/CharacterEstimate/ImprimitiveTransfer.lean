import BombieriVinogradov.Helpers.ComplexAnalysis.ReferenceSumComparison
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.ChebyshevCorrectionDecay
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.ExceptionalChoiceDecay
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring

/-!
# Transfer of a primitive character estimate

The character and exceptional-choice corrections are added separately.
This fixed-parameter lemma preserves the rate and both faithful choices.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem characterChebyshevExceptional_of_primitive_bound
    {c a C : Real} (hc : 0 < c) (hHalf : a <= (1 / 2 : Real))
    (hRate : a <= c / 4) {N x : Nat} [NeZero N] (hN : 3 <= N)
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1)
    (hData : ExplicitFormulaZeroFreeData c chi.primitiveCharacter)
    (e ep : Option Complex) (hAmbient : IsExceptionalZeroChoice c chi e)
    (hPrimitive : IsExceptionalZeroChoice c chi.primitiveCharacter ep)
    (hx : 3 <= x)
    (hMod : (N : Real) <= Real.exp (Real.sqrt (Real.log x)))
    (hBound : norm (characterChebyshevSum x chi.primitiveCharacter +
      exceptionalZeroContribution x ep) <=
        C * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x))))) :
    norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) <=
      (C + 48 / Real.log (2 : Real) + 4 / 3) *
        ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  let F : Real := (x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))
  change norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) <=
    (C + 48 / Real.log (2 : Real) + 4 / 3) * F
  have hEuler : norm (characterChebyshevSum x chi -
      characterChebyshevSum x chi.primitiveCharacter) <=
        (48 / Real.log (2 : Real)) * F := by
    simpa only [F] using
      norm_characterChebyshevSum_sub_primitive_le_exp hHalf hN chi hx hMod
  have hChoice : norm (exceptionalZeroContribution x e -
      exceptionalZeroContribution x ep) <= (4 / 3 : Real) * F := by
    simpa only [F] using norm_exceptionalChoice_difference_le_exp hc hRate hN
      chi hchi hData e ep hAmbient hPrimitive hx hMod
  calc
    norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) <=
        norm (characterChebyshevSum x chi.primitiveCharacter +
          exceptionalZeroContribution x ep) +
        norm (characterChebyshevSum x chi -
          characterChebyshevSum x chi.primitiveCharacter) +
        norm (exceptionalZeroContribution x e - exceptionalZeroContribution x ep) :=
      BombieriVinogradov.ComplexAnalysis.norm_sum_le_reference_and_differences
        (characterChebyshevSum x chi) (exceptionalZeroContribution x e)
        (characterChebyshevSum x chi.primitiveCharacter) (exceptionalZeroContribution x ep)
    _ <= C * F + (48 / Real.log (2 : Real)) * F + (4 / 3 : Real) * F :=
      add_le_add (add_le_add hBound hEuler) hChoice
    _ = (C + 48 / Real.log (2 : Real) + 4 / 3) * F := by ring

end BombieriVinogradov.SiegelWalfisz
