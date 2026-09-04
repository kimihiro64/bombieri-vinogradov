import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# The uniform Siegel gap for an exceptional zero

The real nonvanishing interval excludes every selected exceptional zero
from its interior. The coefficient is fixed before all character data.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_exceptionalZero_siegelGap
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists k : Real, And (0 < k)
      (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
        Ne chi 1 -> forall {c : Real}, ExplicitFormulaZeroFreeData c chi ->
          forall {beta : Complex}, IsExceptionalZero c chi beta ->
            k * (N : Real) ^ (-epsilon) <= 1 - beta.re) := by
  classical
  choose k hk hExclusion using siegelZeroExclusion_nonprincipal epsilon hepsilon
  refine Exists.intro k (And.intro hk ?_)
  intro N inst chi hchi c hData beta hBeta
  have hQuadratic : chi ^ 2 = 1 := (hData.exceptional beta hBeta).quadratic
  have hReal : (beta.re : Complex) = beta := Complex.ext rfl hBeta.2.1.symm
  have hZero : chi.LFunction (beta.re : Complex) = 0 := by
    rw [hReal]
    exact hBeta.1
  by_cases hGap : k * (N : Real) ^ (-epsilon) <= 1 - beta.re
  case pos => exact hGap
  case neg =>
    have hWindow : 1 - k * (N : Real) ^ (-epsilon) < beta.re := by linarith
    exact False.elim (hExclusion N chi hQuadratic hchi beta.re hWindow hZero)

end BombieriVinogradov.SiegelWalfisz
