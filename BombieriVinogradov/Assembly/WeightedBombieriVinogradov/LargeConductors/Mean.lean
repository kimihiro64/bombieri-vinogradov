import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.LargeConductors.Cumulative
import BombieriVinogradov.Definitions.PrimitiveConductorWeight
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveConductorWeight
import BombieriVinogradov.Helpers.RealAnalysis.LogProductCutoff
import BombieriVinogradov.Helpers.RealAnalysis.QuadraticCumulativeTail
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The large-conductor primitive maximal mean

Vaughan's cumulative bound enters reciprocal Abel summation without discarding
its conductor weights or any outer logarithmic factor.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- A uniform reciprocal-totient bound for primitive nonprincipal large conductors. -/
theorem large_conductor_primitive_mean :
    exists C : Real, And (0 < C)
      (forall {X : Real}, 2 <= X -> forall R Q : Nat, 1 <= R -> R <= Q ->
        Finset.sum (Finset.Ioc R Q)
            (fun d => nonprincipalPrimitiveMaximalSum X d / (d.totient : Real)) <=
          (C * Real.log (X * (Q : Real)) ^ 3) *
            (2 * X / (R : Real) + X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real)) +
              2 * X ^ (1 / 2 : Real) * (Q : Real))) := by
  choose C hC hCumulative using vaughan_cumulative_envelope
  refine Exists.intro C (And.intro hC ?_)
  intro X hX R Q hR hRQ
  have hXOne : 1 <= X := by linarith
  have hXPos : 0 < X := by linarith
  have hLog := RealAnalysis.log_mul_nat_nonneg hXOne (hR.trans hRQ)
  have hScale : 0 <= C * Real.log (X * (Q : Real)) ^ 3 := by positivity
  have hTail := RealAnalysis.sum_Ioc_div_le_of_scaled_quadratic_partial_sums
    (fun d => nonprincipalPrimitiveConductorWeight X d)
    (C * Real.log (X * (Q : Real)) ^ 3) X (X ^ (5 / 6 : Real)) (X ^ (1 / 2 : Real))
    hScale hXPos.le (by positivity) (by positivity)
    (fun d => nonprincipalPrimitiveConductorWeight_nonneg X d) hR hRQ
    (fun k hk hkQ => hCumulative (X := X) hX Q k hk hkQ)
  calc
    Finset.sum (Finset.Ioc R Q)
        (fun d => nonprincipalPrimitiveMaximalSum X d / (d.totient : Real)) =
        Finset.sum (Finset.Ioc R Q)
          (fun d => nonprincipalPrimitiveConductorWeight X d / (d : Real)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdPos : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hR.trans (Finset.mem_Ioc.mp hd).1.le)
      exact (nonprincipalPrimitiveConductorWeight_div X hdPos).symm
    _ <= (C * Real.log (X * (Q : Real)) ^ 3) *
        (2 * X / (R : Real) + X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real)) +
          2 * X ^ (1 / 2 : Real) * (Q : Real)) := hTail

end BombieriVinogradov.WeightedBombieriVinogradov
