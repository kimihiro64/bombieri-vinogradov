import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.ExceptionalCenteringCorrectionBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Positivity

/-!
# Both cases of the exceptional centering correction

A faithful optional exceptional zero contributes either zero or the
previously bounded simple real pair, with one common error majorant.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_optionalExceptionalCenteringCorrection_le
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hx : 2 < x) {c : Real} (hData : ExplicitFormulaZeroFreeData c chi)
    (exceptional : Option Complex)
    (hChoice : IsExceptionalZeroChoice c chi exceptional) :
    norm (centeredExceptionalResidueSum chi x exceptional +
        exceptionalZeroContribution x exceptional) <=
      (4 / 3 : Real) + (x : Real) ^ (1 / 4 : Real) * Real.log x := by
  cases exceptional
  case none =>
    simp only [centeredExceptionalResidueSum_none, exceptionalZeroContribution,
      add_zero, norm_zero]
    positivity
  case some beta =>
    have hExceptional : IsExceptionalZero c chi beta := hChoice
    have hFacts := hData.exceptional beta hExceptional
    exact norm_centeredExceptionalResidueSum_add_exceptionalZeroContribution_le
      hchi hPrimitive hFacts.quadratic hx hExceptional
      hFacts.simple hFacts.reflection_ne hFacts.re_lower

end BombieriVinogradov.SiegelWalfisz
