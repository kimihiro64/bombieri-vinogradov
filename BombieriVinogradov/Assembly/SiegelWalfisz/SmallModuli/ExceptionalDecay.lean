import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.SmallModuli.ExceptionalPowerDecay
import BombieriVinogradov.Proof.SiegelWalfisz.SmallModuli.SiegelExceptionalGap
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform exceptional-contribution decay for small moduli

Siegel's coefficient is chosen before all characters and faithful choices.
The target rate is fixed; only the multiplicative coefficient depends
on that rate and the logarithmic modulus exponent.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_exceptionalContribution_le_polylog_decay
    {a A : Real} (ha : 0 <= a) (hA : 0 < A) :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
        Ne chi 1 -> forall {c : Real}, ExplicitFormulaZeroFreeData c chi ->
          forall {x : Nat}, 2 <= x -> (N : Real) <= (Real.log x) ^ A ->
            forall e : Option Complex, IsExceptionalZeroChoice c chi e ->
              norm (exceptionalZeroContribution x e) <=
                K * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x))))) := by
  classical
  have hEpsilon : 0 < 1 / (3 * A) := by positivity
  choose k hk hGap using exists_exceptionalZero_siegelGap hEpsilon
  refine Exists.intro ((4 / 3 : Real) * Real.exp (a ^ 4 / k ^ 3))
    (And.intro (by positivity) ?_)
  intro N inst chi hchi c hData x hx hMod e hChoice
  cases e
  case none =>
    change norm (0 : Complex) <= _
    rw [norm_zero]
    positivity
  case some beta =>
    have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
    have hNReal : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
    have hNPos : (0 : Real) < (N : Real) := by linarith
    have hLower : (3 / 4 : Real) <= beta.re :=
      (hData.exceptional beta hChoice).re_lower
    exact norm_exceptionalPower_le_polylog_decay ha hA hk hNPos hx hMod hLower
      (hGap chi hchi hData hChoice)

end BombieriVinogradov.SiegelWalfisz
