import BombieriVinogradov.Assembly.VaughanMeanValue.MaximalBilinear
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanAssembly
import Mathlib.Tactic

/-!
# Bilinear encoding for the outer Vaughan range

The maximal von Mangoldt character sum is represented exactly as a maximal
bilinear sum with a one-point left factor. Coefficient masses are owned by the
separate outer-range mass module.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

def outerRangeUnitCoefficient (_ : Nat) : Complex := 1

def outerRangeMangoldtCoefficient (n : Nat) : Complex :=
  (ArithmeticFunction.vonMangoldt n : Complex)

theorem outerRangeRestrictedSum_eq
    (X Y q : Nat) (chi : DirichletCharacter Complex q) (hYX : Y <= X) :
    restrictedBilinearCharacterSum outerRangeUnitCoefficient
        outerRangeMangoldtCoefficient 1 X Y q chi =
      psiCharacterSum Y q chi := by
  unfold restrictedBilinearCharacterSum psiCharacterSum
  simp [outerRangeUnitCoefficient, outerRangeMangoldtCoefficient]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

theorem maximalBilinearNorm_outerRange_eq
    (X q : Nat) (chi : DirichletCharacter Complex q) :
    maximalBilinearNorm outerRangeUnitCoefficient
        outerRangeMangoldtCoefficient 1 X X chi =
      maximalMangoldtCharacterNorm X q chi := by
  unfold maximalBilinearNorm maximalMangoldtCharacterNorm
  apply Finset.sup'_congr (H := by simp) rfl
  intro Y hY
  have hYX : Y <= X := Nat.le_of_lt_succ (Finset.mem_range.mp hY)
  rw [outerRangeRestrictedSum_eq X Y q chi hYX]
  rfl

end BombieriVinogradov.VaughanMeanValue
