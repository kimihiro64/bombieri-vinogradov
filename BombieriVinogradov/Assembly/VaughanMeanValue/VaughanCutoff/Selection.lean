import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.MiddleLevel
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.OuterRange
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.SmallLevel
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.UpperLevel
import Mathlib.Tactic

/-!
# Exhaustive Vaughan cutoff selection

The four proved range estimates are selected by natural-number case analysis.
This module contains no new analytic estimate.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem vaughanMean_le_sourceScale_nat
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  by_cases hOuter : X <= Q ^ 2
  · have hbound := vaughanMean_le_outerRange X Q hX hQ hOuter
    have hS : 0 <= vaughanSourceScale X Q := by
      dsimp [vaughanSourceScale]
      positivity
    have hL : 0 <= vaughanLogScale X Q :=
      (by norm_num : (0 : Real) <= 1 / 2).trans
        (half_le_vaughanLogScale X Q hX hQ)
    have hproduct : 0 <= vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 :=
      mul_nonneg hS (pow_nonneg hL 3)
    have hconstants := mul_le_mul_of_nonneg_right
      (by norm_num : (6480 : Real) <= 200000) hproduct
    exact hbound.trans (by simpa [mul_assoc] using hconstants)
  · have hInner : Q ^ 2 <= X := by omega
    by_cases hSmall : Q ^ 6 <= X
    · exact vaughanMean_le_smallLevel X Q hX hQ hSmall
    · by_cases hMiddle : Q ^ 3 <= X
      · exact vaughanMean_le_middleLevel X Q hX hQ hMiddle
      · have hUpper : X <= Q ^ 3 := by omega
        exact vaughanMean_le_upperLevel X Q hX hQ hInner hUpper

end BombieriVinogradov.VaughanMeanValue
