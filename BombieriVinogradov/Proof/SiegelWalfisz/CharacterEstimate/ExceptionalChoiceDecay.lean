import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.PrimitiveOnlyExceptionalDecay
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ExceptionalChoice
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform decay of the exceptional-choice difference

Faithful ambient and primitive choices agree whenever an ambient zero
exists. A primitive-only zero is controlled by its proved ambient gap.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_exceptionalChoice_difference_le_exp
    {c a : Real} (hc : 0 < c) (hRate : a <= c / 4)
    {N x : Nat} [NeZero N] (hN : 3 <= N)
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1)
    (hData : ExplicitFormulaZeroFreeData c chi.primitiveCharacter)
    (e ep : Option Complex) (hAmbient : IsExceptionalZeroChoice c chi e)
    (hPrimitive : IsExceptionalZeroChoice c chi.primitiveCharacter ep)
    (hx : 3 <= x)
    (hMod : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    norm (exceptionalZeroContribution x e - exceptionalZeroContribution x ep) <=
      (4 / 3 : Real) * ((x : Real) *
        Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  cases e
  case none =>
    cases ep
    case none =>
      rw [sub_self, norm_zero]
      positivity
    case some beta =>
      have hBound := norm_primitiveOnlyExceptionalContribution_le_exp hc hRate hN
        chi hchi hData hAmbient hPrimitive hx hMod
      change norm ((0 : Complex) - exceptionalZeroContribution x (some beta)) <= _
      have hNeg : (0 : Complex) - exceptionalZeroContribution x (some beta) =
          -exceptionalZeroContribution x (some beta) := by ring
      rw [hNeg, norm_neg]
      exact hBound
  case some beta =>
    have hEq := primitiveExceptionalChoice_eq_some_of_ambient
      hc chi hchi hData ep hPrimitive hAmbient
    rw [hEq, sub_self, norm_zero]
    positivity

end BombieriVinogradov.SiegelWalfisz
