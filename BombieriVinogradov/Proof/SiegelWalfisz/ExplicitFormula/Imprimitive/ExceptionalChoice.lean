import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ExceptionalPredicate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith

/-!
# Compatibility of exceptional choices across levels

Whenever the ambient character selects a zero, every faithful choice for
its primitive character selects that same zero.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem primitiveExceptionalChoice_eq_some_of_ambient
    {c : Real} (hc : 0 < c) {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1)
    (hData : ExplicitFormulaZeroFreeData c chi.primitiveCharacter)
    (e : Option Complex) (hChoice : IsExceptionalZeroChoice c chi.primitiveCharacter e)
    {beta : Complex} (hAmbient : IsExceptionalZero c chi beta) :
    e = some beta := by
  have hBeta : IsExceptionalZero c chi.primitiveCharacter beta :=
    isExceptionalZero_primitive_of_isExceptionalZero hc chi hchi hAmbient
  cases e
  case none =>
    change Not (exists rho : Complex,
      IsExceptionalZero c chi.primitiveCharacter rho) at hChoice
    exact False.elim (hChoice (Exists.intro beta hBeta))
  case some gamma =>
    change IsExceptionalZero c chi.primitiveCharacter gamma at hChoice
    have hGammaGap : 1 - gamma.re <= c / Real.log chi.conductor := by
      linarith [hChoice.2.2.2.2]
    have hBetaGap : 1 - beta.re <= c / Real.log chi.conductor := by
      linarith [hBeta.2.2.2.2]
    have hEq : gamma = beta := hData.realUnique gamma beta
      hChoice.2.2.1 hBeta.2.2.1 hChoice.1 hBeta.1
      hChoice.2.1 hBeta.2.1 hGammaGap hBetaGap
    exact congrArg Option.some hEq

end BombieriVinogradov.SiegelWalfisz
