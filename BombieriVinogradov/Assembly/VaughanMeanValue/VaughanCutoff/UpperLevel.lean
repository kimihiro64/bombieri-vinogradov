import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.Core
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.UpperLevelAlgebra
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.UpperLevelCutoff
import Mathlib.Tactic

/-!
# Vaughan estimate in the upper inner-level regime

This module composes the ceiling cutoff near `X/Q^2` and the four proved real
inequalities under `Q^2 <= X <= Q^3` with the common cutoff interface.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem vaughanMean_le_upperLevel
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q)
    (hqSqX : Q ^ 2 <= X) (hxCube : X <= Q ^ 3) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  let u := upperLevelCutoff X Q
  have hxReal : (1 : Real) <= (X : Real) := by exact_mod_cast (show 1 <= X by omega)
  have hqReal : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  have hqSqXReal : (Q : Real) ^ 2 <= (X : Real) := by exact_mod_cast hqSqX
  have hxCubeReal : (X : Real) <= (Q : Real) ^ 3 := by exact_mod_cast hxCube
  have hratioU : upperLevelRatio (X : Real) (Q : Real) <= (u : Real) := by
    simpa [u] using upperLevelRatio_le_cutoff X Q
  have huRatio : (u : Real) <= upperLevelRatio (X : Real) (Q : Real) + 1 := by
    exact (by simpa [u] using (upperLevelCutoff_lt_ratio_add_one X Q).le)
  have hx0 : (0 : Real) <= (X : Real) := by positivity
  have hmiddle :
      0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
  have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
  have hmiddleLastScale :
      (X : Real) ^ (5 / 6 : Real) * (Q : Real) +
          Real.sqrt (X : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hlastScale :
      Real.sqrt (X : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hxLastScale :
      (X : Real) + Real.sqrt (X : Real) * (Q : Real) ^ 2 <=
        vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  apply vaughanMean_le_of_cutoff_bounds u X Q
  · simpa [u] using upperLevelCutoff_one_le X Q hX hQ
  · simpa [u] using upperLevelCutoff_le X Q hQ
  · exact hX
  · exact hQ
  · exact (upperLevelSmallTerm_le hxReal hqReal hqSqXReal hxCubeReal huRatio).trans
      hmiddleLastScale
  · exact (upperLevelInverseTerm_le hxReal hqReal hratioU).trans hlastScale
  · exact (upperLevelForwardTerm_le hxReal hqReal hxCubeReal huRatio).trans
      hmiddleLastScale
  · exact (upperLevelShortTerm_le hxReal hqReal huRatio).trans hxLastScale

end BombieriVinogradov.VaughanMeanValue
