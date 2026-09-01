import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.OuterRangeCoefficients
import Mathlib.Tactic

/-!
# Coefficient masses for the outer Vaughan range

The one-point unit sequence has mass one, while the von Mangoldt sequence
through `X` has mass at most `X * log(X)^2`. Exact bilinear encoding and the
outer-range aggregate remain in separate modules.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

theorem outerRangeUnitCoefficient_mass :
    coefficientMass outerRangeUnitCoefficient 1 = 1 := by
  simp [coefficientMass, outerRangeUnitCoefficient]

theorem outerRangeMangoldtCoefficient_norm_le
    (X n : Nat) (hn : n ∈ Finset.Icc 1 X) :
    ‖outerRangeMangoldtCoefficient n‖ <= Real.log (X : Real) := by
  have hnBounds := Finset.mem_Icc.mp hn
  rw [outerRangeMangoldtCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hnBounds.2))

theorem outerRangeMangoldtCoefficient_mass_le (X : Nat) :
    coefficientMass outerRangeMangoldtCoefficient X <=
      (X : Real) * Real.log (X : Real) ^ 2 := by
  unfold coefficientMass
  have hlog : 0 <= Real.log (X : Real) := Real.log_natCast_nonneg X
  calc
    ∑ n ∈ Icc 1 X, ‖outerRangeMangoldtCoefficient n‖ ^ 2 <=
        ∑ n ∈ Icc 1 X, Real.log (X : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [norm_nonneg (outerRangeMangoldtCoefficient n),
        outerRangeMangoldtCoefficient_norm_le X n hn]
    _ = (X : Real) * Real.log (X : Real) ^ 2 := by simp

end BombieriVinogradov.VaughanMeanValue
