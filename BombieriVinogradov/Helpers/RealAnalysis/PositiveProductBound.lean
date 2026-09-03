import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive product bound for normalized horizontal terms
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem normalized_horizontal_product_le
    {C Z2 X H W T L2 : Real}
    (hC : 0 <= C) (hX : 0 <= X)
    (hT : 0 < T) (hTH : T <= H)
    (hZ : Z2 <= 9 * L2) (hL2 : 0 <= L2)
    (hW0 : 0 <= W) (hW : W <= 3) :
    (1 / (2 * Real.pi)) * ((C * Z2) * (4 * X / H) * W) <=
      (54 / Real.pi) * C * (X / T * L2) := by
  have hH : 0 < H := hT.trans_le hTH
  have hPiFactorNonneg : 0 <= 1 / (2 * Real.pi) := by positivity
  have hCZ :
      C * Z2 <= C * (9 * L2) :=
    mul_le_mul_of_nonneg_left hZ hC
  have hHeight :
      4 * X / H <= 4 * X / T :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) hX) hT hTH
  have hLowerHeight : 0 <= 4 * X / H :=
    div_nonneg (mul_nonneg (by norm_num) hX) hH.le
  have hUpperScale : 0 <= C * (9 * L2) :=
    mul_nonneg hC (mul_nonneg (by norm_num) hL2)
  have hUpperHeight : 0 <= 4 * X / T :=
    div_nonneg (mul_nonneg (by norm_num) hX) hT.le
  have hTwoFactors :
      (C * Z2) * (4 * X / H) <=
        (C * (9 * L2)) * (4 * X / T) := by
    apply (mul_le_mul_of_nonneg_right hCZ hLowerHeight).trans
    exact mul_le_mul_of_nonneg_left hHeight hUpperScale
  have hUpperTwoFactors :
      0 <= (C * (9 * L2)) * (4 * X / T) :=
    mul_nonneg hUpperScale hUpperHeight
  have hThreeFactors :
      (C * Z2) * (4 * X / H) * W <=
        (C * (9 * L2)) * (4 * X / T) * 3 := by
    apply (mul_le_mul_of_nonneg_right hTwoFactors hW0).trans
    exact mul_le_mul_of_nonneg_left hW hUpperTwoFactors
  calc
    (1 / (2 * Real.pi)) * ((C * Z2) * (4 * X / H) * W) <=
        (1 / (2 * Real.pi)) *
          ((C * (9 * L2)) * (4 * X / T) * 3) :=
      mul_le_mul_of_nonneg_left hThreeFactors hPiFactorNonneg
    _ = (54 / Real.pi) * C * (X / T * L2) := by ring

end BombieriVinogradov.RealAnalysis
