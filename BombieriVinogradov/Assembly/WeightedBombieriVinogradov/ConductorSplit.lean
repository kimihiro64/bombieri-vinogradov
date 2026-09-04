import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.LargeConductors.Mean
import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.SmallConductors.Mean
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveMaximalNonneg
import BombieriVinogradov.Helpers.RealAnalysis.LogProductCutoff
import BombieriVinogradov.Helpers.RealAnalysis.PositiveIntervalSplit
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Combining small and large primitive conductors

The rate and Vaughan constant precede the logarithmic cutoff exponent.
The empty-tail branch permits the chosen cutoff to exceed the outer modulus.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Uniform primitive-mean control at any admissible small-conductor cutoff. -/
theorem primitive_conductor_mean_split :
    exists a Cv : Real, And (0 < a) (And (0 < Cv)
      (forall B : Real, 0 < B -> exists Cs : Real, And (0 < Cs)
        (forall {X : Real}, Real.exp (4 : Real) <= X -> forall R Q : Nat,
          1 <= R -> (R : Real) <= (Real.log X) ^ B -> 1 <= Q ->
          primitiveConductorMean X Q <=
            Cs * ((R : Real) * X * Real.exp (-(a * Real.sqrt (Real.log X)))) +
              (Cv * Real.log (X * (Q : Real)) ^ 3) *
                (2 * X / (R : Real) + X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real)) +
                  2 * X ^ (1 / 2 : Real) * (Q : Real))))) := by
  choose a ha hSmall using small_conductor_primitive_mean
  choose Cv hCv hLarge using large_conductor_primitive_mean
  refine Exists.intro a (Exists.intro Cv (And.intro ha (And.intro hCv ?_)))
  intro B hB
  choose Cs hCs hSmallB using hSmall B hB
  refine Exists.intro Cs (And.intro hCs ?_)
  intro X hX R Q hR hRPoly hQ
  have hExp := Real.add_one_le_exp (4 : Real)
  have hXTwo : 2 <= X := by linarith
  have hXOne : 1 <= X := by linarith
  have hXPos : 0 < X := by linarith
  have hQRaw : (((1 : Nat) : Real) <= (Q : Real)) := Nat.cast_le.mpr hQ
  have hQReal : (1 : Real) <= (Q : Real) := by simpa only [Nat.cast_one] using hQRaw
  have hLogQ := Real.log_nonneg hQReal
  have hLogProduct := RealAnalysis.log_mul_nat_nonneg hXOne hQ
  have hTail :
      Finset.sum (Finset.Ioc R Q)
        (fun d => nonprincipalPrimitiveMaximalSum X d / (d.totient : Real)) <=
      (Cv * Real.log (X * (Q : Real)) ^ 3) *
        (2 * X / (R : Real) + X ^ (5 / 6 : Real) * (2 + Real.log (Q : Real)) +
          2 * X ^ (1 / 2 : Real) * (Q : Real)) := by
    by_cases hRQ : R <= Q
    case pos => exact hLarge (X := X) hXTwo R Q hR hRQ
    case neg =>
      have hQR : Q <= R := (Nat.lt_of_not_ge hRQ).le
      rw [Finset.Ioc_eq_empty_of_le hQR, Finset.sum_empty]
      positivity
  have hSplit : primitiveConductorMean X Q <= primitiveConductorMean X R +
      Finset.sum (Finset.Ioc R Q)
        (fun d => nonprincipalPrimitiveMaximalSum X d / (d.totient : Real)) := by
    unfold primitiveConductorMean
    exact RealAnalysis.sum_Icc_le_sum_Icc_add_sum_Ioc
      (fun d => nonprincipalPrimitiveMaximalSum X d / (d.totient : Real))
      (fun d => div_nonneg (nonprincipalPrimitiveMaximalSum_nonneg X d)
        (Nat.cast_nonneg d.totient)) R Q
  exact hSplit.trans (add_le_add (hSmallB (X := X) hX R hRPoly) hTail)

end BombieriVinogradov.WeightedBombieriVinogradov
