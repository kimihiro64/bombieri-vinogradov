import BombieriVinogradov.Assembly.SiegelWalfisz.CharacterEstimate.ExceptionalMain
import BombieriVinogradov.Assembly.SiegelWalfisz.SmallModuli.LargeHeight
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.UniformData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.SmallModuli.BoundedHeight
import BombieriVinogradov.Proof.SiegelWalfisz.SmallModuli.HeightSplit
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The character-form Siegel-Walfisz theorem

There is one absolute exponential rate. For each logarithmic modulus
exponent, one coefficient covers every nonprincipal character and all
natural endpoints at least two.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegel_walfisz :
    exists a : Real, And (0 < a)
      (forall A : Real, 0 < A -> exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
          Ne chi 1 -> forall {x : Nat}, 2 <= x ->
            (N : Real) <= (Real.log x) ^ A ->
              norm (characterChebyshevSum x chi) <=
                C * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))))) := by
  classical
  choose c a C0 hUniform using characterChebyshevExceptional
  refine Exists.intro a (And.intro hUniform.a_pos ?_)
  intro A hA
  choose K hK hLarge using exists_largeHeight_character_bound hUniform hA
  let B : Real := (1 + 16 * A ^ 2) ^ 2 * Real.exp (a * (1 + 16 * A ^ 2))
  have hB : 0 <= B := by
    dsimp [B]
    positivity
  have hC0 : 0 < C0 := hUniform.C_pos
  have hCoefficient : 0 < C0 + K + B := by linarith
  have hLargeCoefficient : C0 + K <= C0 + K + B := by linarith
  have hSmallCoefficient : B <= C0 + K + B := by linarith
  refine Exists.intro (C0 + K + B) (And.intro hCoefficient ?_)
  intro N inst chi hchi x hx hMod
  have hScale : 0 <= (x : Real) * Real.exp (-(a * Real.sqrt (Real.log x))) := by
    positivity
  cases sqrtLog_height_split A hx
  case inl hHeight =>
    exact (hLarge chi hchi hHeight.1 hMod hHeight.2).trans
      (mul_le_mul_of_nonneg_right hLargeCoefficient hScale)
  case inr hHeight =>
    have hBound : norm (characterChebyshevSum x chi) <=
        B * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) :=
      norm_characterChebyshevSum_le_boundedHeight hUniform.a_pos.le chi hx hHeight
    exact hBound.trans (mul_le_mul_of_nonneg_right hSmallCoefficient hScale)

end BombieriVinogradov.SiegelWalfisz
