import BombieriVinogradov.Assembly.SiegelWalfisz.Main
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.RealAnalysis.PolylogConductorTransfer
import BombieriVinogradov.Helpers.RealAnalysis.SqrtEndpointDecay
import BombieriVinogradov.Helpers.RealAnalysis.SqrtEndpointLog
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Uniform Siegel-Walfisz control above the square-root endpoint

Apply the proved character theorem at twice the logarithmic modulus exponent.
The coefficient is chosen before the modulus, character, real cutoff and endpoint.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- One absolute rate controls every large endpoint at a polylogarithmic modulus. -/
theorem siegel_walfisz_large_endpoint :
    exists a : Real, And (0 < a)
      (forall B : Real, 0 < B -> exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
          Ne chi 1 -> forall {X : Real}, 0 < X -> 4 <= Real.log X ->
            (N : Real) <= (Real.log X) ^ B -> forall {y : Nat},
              Real.sqrt X <= (y : Real) -> (y : Real) <= X ->
                norm (VaughanMeanValue.psiCharacterSum y N chi) <=
                  C * (X * Real.exp (-(a * Real.sqrt (Real.log X)))))) := by
  choose a ha hSW using SiegelWalfisz.siegel_walfisz
  refine Exists.intro (a / 2) (And.intro (by linarith) ?_)
  intro B hB
  have hTwiceB : 0 < 2 * B := by linarith
  choose C hC hPointwise using hSW (2 * B) hTwiceB
  refine Exists.intro C (And.intro hC ?_)
  intro N inst chi hchi X hX hLogFour hMod y hyRoot hyX
  have hSize := Real.log_le_sub_one_of_pos hX
  have hXOne : 1 <= X := by linarith
  have hyPos : 0 < (y : Real) := (Real.sqrt_pos.mpr hX).trans_le hyRoot
  have hLogCompare := RealAnalysis.log_le_two_mul_log_of_sqrt_le hXOne hyRoot
  have hYSize := Real.log_le_sub_one_of_pos hyPos
  have hYTwoReal : (2 : Real) <= (y : Real) := by linarith
  have hYTwoCast : (((2 : Nat) : Real) <= (y : Real)) := by simpa using hYTwoReal
  have hYTwo : 2 <= y := Nat.cast_le.mp hYTwoCast
  have hModY : (N : Real) <= (Real.log y) ^ (2 * B) :=
    hMod.trans (RealAnalysis.rpow_le_rpow_twice_of_le_two_mul hLogFour hLogCompare hB.le)
  have hBound : norm (VaughanMeanValue.psiCharacterSum y N chi) <=
      C * ((y : Real) * Real.exp (-(a * Real.sqrt (Real.log y)))) :=
    hPointwise chi hchi hYTwo hModY
  exact hBound.trans (mul_le_mul_of_nonneg_left
    (RealAnalysis.mul_exp_neg_sqrt_log_le_of_sqrt_le hXOne hyRoot hyX ha.le) hC.le)

end BombieriVinogradov.WeightedBombieriVinogradov
