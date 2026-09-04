import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.SmallConductors.Maximal
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveMaximalAverage
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Defs
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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The small-conductor primitive maximal mean

Uniform maximal Siegel-Walfisz bounds survive the reciprocal-totient
character average. Summing positive conductors adds exactly the cutoff factor.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The primitive mean below a polylogarithmic cutoff has uniform exponential decay. -/
theorem small_conductor_primitive_mean :
    exists a : Real, And (0 < a)
      (forall B : Real, 0 < B -> exists C : Real, And (0 < C)
        (forall {X : Real}, Real.exp (4 : Real) <= X -> forall R : Nat,
          (R : Real) <= (Real.log X) ^ B ->
            primitiveConductorMean X R <=
              C * ((R : Real) * X * Real.exp (-(a * Real.sqrt (Real.log X)))))) := by
  choose a ha hUniform using maximal_siegel_walfisz
  refine Exists.intro a (And.intro ha ?_)
  intro B hB
  choose C hC hMax using hUniform B hB
  refine Exists.intro C (And.intro hC ?_)
  intro X hX R hR
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hScale : 0 <= C * (X * Real.exp (-(a * Real.sqrt (Real.log X)))) := by
    positivity
  unfold primitiveConductorMean
  calc
    Finset.sum (Finset.Icc 1 R)
        (fun q => nonprincipalPrimitiveMaximalSum X q / (q.totient : Real)) <=
        Finset.sum (Finset.Icc 1 R)
          (fun _ => C * (X * Real.exp (-(a * Real.sqrt (Real.log X))))) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : 0 < q :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
      let : NeZero q := NeZero.mk (Nat.ne_of_gt hqPos)
      have hqR : (q : Real) <= (R : Real) := Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2
      have hMod : (q : Real) <= (Real.log X) ^ B := hqR.trans hR
      exact nonprincipalPrimitiveMaximalSum_div_totient_le hScale
        (fun chi hchi => hMax chi hchi (X := X) hX hMod)
    _ = (R : Real) * (C * (X * Real.exp (-(a * Real.sqrt (Real.log X))))) := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = C * ((R : Real) * X * Real.exp (-(a * Real.sqrt (Real.log X)))) := by ring

end BombieriVinogradov.WeightedBombieriVinogradov
