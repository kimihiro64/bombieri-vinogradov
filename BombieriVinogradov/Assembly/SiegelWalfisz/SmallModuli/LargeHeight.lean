import BombieriVinogradov.Assembly.SiegelWalfisz.SmallModuli.ExceptionalDecay
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.UniformData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.FaithfulChoice
import BombieriVinogradov.Proof.SiegelWalfisz.SmallModuli.ModulusRange
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Uniform character bound in the large-height small-modulus range

The faithful exceptional term is removed at the already fixed rate.
Its coefficient is chosen before the character and endpoint.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_largeHeight_character_bound
    {c a C A : Real} (hUniform : CharacterEstimateData c a C) (hA : 0 < A) :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
        Ne chi 1 -> forall {x : Nat}, 3 <= x ->
          (N : Real) <= (Real.log x) ^ A ->
            16 * A ^ 2 <= Real.sqrt (Real.log x) ->
              norm (characterChebyshevSum x chi) <=
                (C + K) * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x))))) := by
  classical
  choose K hK hExceptional using
    exists_norm_exceptionalContribution_le_polylog_decay hUniform.a_pos.le hA
  refine Exists.intro K (And.intro hK ?_)
  intro N inst chi hchi x hx hMod hHeight
  choose e hChoice using exists_faithfulExceptionalChoice c chi
  have hxTwo : 2 <= x := Nat.le_trans (by decide) hx
  have hMain := hUniform.estimate hchi hx
    (modulus_le_exp_sqrtLog_of_large hA.le hx hMod hHeight) e hChoice
  have hError := hExceptional chi hchi (hUniform.zeroFree chi hchi)
    hxTwo hMod e hChoice
  calc
    norm (characterChebyshevSum x chi) =
        norm ((characterChebyshevSum x chi + exceptionalZeroContribution x e) -
          exceptionalZeroContribution x e) := by
      congr 1
      ring
    _ <= norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) +
        norm (exceptionalZeroContribution x e) := norm_sub_le _ _
    _ <= C * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) +
        K * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) :=
      add_le_add hMain hError
    _ = (C + K) * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by ring

end BombieriVinogradov.SiegelWalfisz
