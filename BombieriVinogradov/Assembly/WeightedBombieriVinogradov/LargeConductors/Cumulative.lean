import BombieriVinogradov.Assembly.VaughanMeanValue.RealEndpoint.Main
import BombieriVinogradov.Definitions.PrimitiveConductorWeight
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveCumulativeComparison
import BombieriVinogradov.Helpers.RealAnalysis.LogProductCutoff
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vaughan's cumulative bound with a common conductor logarithm

The absolute mean-value constant is selected before every endpoint and cutoff.
Only the logarithmic factor is enlarged to the outer conductor cutoff.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- A uniform quadratic cumulative bound for the nonprincipal primitive conductor weight. -/
theorem vaughan_cumulative_envelope :
    exists C : Real, And (0 < C)
      (forall {X : Real}, 2 <= X -> forall Q k : Nat, 1 <= k -> k <= Q ->
        Finset.sum (Finset.Icc 1 k) (fun d => nonprincipalPrimitiveConductorWeight X d) <=
          (C * Real.log (X * (Q : Real)) ^ 3) *
            (X + X ^ (5 / 6 : Real) * (k : Real) +
              X ^ (1 / 2 : Real) * (k : Real) ^ 2)) := by
  choose C hC hVaughan using VaughanMeanValue.vaughanMeanValue
  refine Exists.intro C (And.intro hC ?_)
  intro X hX Q k hk hkQ
  have hXOne : 1 <= X := by linarith
  have hXPos : 0 < X := by linarith
  have hLog := RealAnalysis.log_mul_nat_pow_le hXOne hk hkQ 3
  have hScale : 0 <= C * (X + X ^ (5 / 6 : Real) * (k : Real) +
      X ^ (1 / 2 : Real) * (k : Real) ^ 2) := by positivity
  calc
    Finset.sum (Finset.Icc 1 k) (fun d => nonprincipalPrimitiveConductorWeight X d) <=
        VaughanMeanValue.primitivePsiMean X k := sum_conductorWeight_le_primitivePsiMean X k
    _ <= C * VaughanMeanValue.basicMeanValueMajorant X k := hVaughan X k hX hk
    _ = (C * (X + X ^ (5 / 6 : Real) * (k : Real) +
          X ^ (1 / 2 : Real) * (k : Real) ^ 2)) * Real.log (X * (k : Real)) ^ 3 := by
      unfold VaughanMeanValue.basicMeanValueMajorant
      ring
    _ <= (C * (X + X ^ (5 / 6 : Real) * (k : Real) +
          X ^ (1 / 2 : Real) * (k : Real) ^ 2)) * Real.log (X * (Q : Real)) ^ 3 :=
      mul_le_mul_of_nonneg_left hLog hScale
    _ = (C * Real.log (X * (Q : Real)) ^ 3) *
        (X + X ^ (5 / 6 : Real) * (k : Real) +
          X ^ (1 / 2 : Real) * (k : Real) ^ 2) := by ring

end BombieriVinogradov.WeightedBombieriVinogradov
