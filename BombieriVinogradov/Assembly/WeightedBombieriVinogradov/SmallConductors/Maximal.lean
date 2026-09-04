import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.SmallConductors.LargeEndpoint
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.DirichletCharacter.SmallEndpointChebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Maximal Siegel-Walfisz at polylogarithmic conductors

One absolute decay rate controls every natural endpoint through the real cutoff.
The coefficient depends on the modulus exponent, not on the character or endpoint.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The full maximal character estimate needed for small conductors in BV. -/
theorem maximal_siegel_walfisz :
    exists a : Real, And (0 < a)
      (forall B : Real, 0 < B -> exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
          Ne chi 1 -> forall {X : Real}, Real.exp (4 : Real) <= X ->
            (N : Real) <= (Real.log X) ^ B ->
              VaughanMeanValue.maximalPsiNorm X chi <=
                C * (X * Real.exp (-(a * Real.sqrt (Real.log X)))))) := by
  choose a ha hUniform using siegel_walfisz_large_endpoint
  let c : Real := min a (1 / 4 : Real)
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hcRate : c <= a := by
    dsimp [c]
    exact min_le_left a (1 / 4 : Real)
  have hcQuarter : c <= (1 / 4 : Real) := by
    dsimp [c]
    exact min_le_right a (1 / 4 : Real)
  refine Exists.intro c (And.intro hcPos ?_)
  intro B hB
  choose C hC hLarge using hUniform B hB
  refine Exists.intro (C + 32) (And.intro (by linarith) ?_)
  intro N inst chi hchi X hX hMod
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hLogOne : 1 <= Real.log X := by linarith
  have hSize := Real.log_le_sub_one_of_pos hXPos
  have hXOne : 1 <= X := by linarith
  have hScale : 0 <= X * Real.exp (-(c * Real.sqrt (Real.log X))) := by positivity
  have hDecay : Real.exp (-(a * Real.sqrt (Real.log X))) <=
      Real.exp (-(c * Real.sqrt (Real.log X))) :=
    Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_right hcRate (Real.sqrt_nonneg _)))
  unfold VaughanMeanValue.maximalPsiNorm
  apply Finset.sup'_le
  intro y hy
  have hyFloor : y <= Nat.floor X := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  have hyX : (y : Real) <= X := (Nat.le_floor_iff hXPos.le).mp hyFloor
  by_cases hSmall : (y : Real) <= Real.sqrt X
  case pos =>
    exact (VaughanMeanValue.norm_psiCharacterSum_le_smallEndpoint
      chi hXOne hLogOne hcQuarter hSmall).trans
        (mul_le_mul_of_nonneg_right (show (32 : Real) <= C + 32 by linarith) hScale)
  case neg =>
    have hBound := hLarge chi hchi (X := X) hXPos hLogFour hMod
      (y := y) (lt_of_not_ge hSmall).le hyX
    calc
      norm (VaughanMeanValue.psiCharacterSum y N chi) <=
          C * (X * Real.exp (-(a * Real.sqrt (Real.log X)))) := hBound
      _ <= C * (X * Real.exp (-(c * Real.sqrt (Real.log X)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hDecay hXPos.le) hC.le
      _ <= (C + 32) * (X * Real.exp (-(c * Real.sqrt (Real.log X)))) :=
        mul_le_mul_of_nonneg_right (show C <= C + 32 by linarith) hScale

end BombieriVinogradov.WeightedBombieriVinogradov
