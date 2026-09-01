import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.Core
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.MiddleLevelAlgebra
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.MiddleLevelCutoff
import Mathlib.Tactic

/-!
# Vaughan estimate in the middle-level regime

This module composes the ceiling cutoff near `X^(1/3)` and the four proved real
inequalities under `Q^3 <= X` with the common cutoff interface.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem vaughanMean_le_middleLevel
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) (hqCubeX : Q ^ 3 <= X) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  let u := middleLevelCutoff X
  have hxReal : (1 : Real) <= (X : Real) := by exact_mod_cast (show 1 <= X by omega)
  have hqReal : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  have hqCubeXReal : (Q : Real) ^ 3 <= (X : Real) := by exact_mod_cast hqCubeX
  have hrootU : middleLevelRoot (X : Real) <= (u : Real) := by
    simpa [u] using middleLevelRoot_le_cutoff X
  have huRoot : (u : Real) <= middleLevelRoot (X : Real) + 1 := by
    exact (by simpa [u] using (middleLevelCutoff_lt_root_add_one X).le)
  have hx0 : (0 : Real) <= (X : Real) := by positivity
  have hmiddle :
      0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
  have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
  have hmiddleLastScale :
      (X : Real) ^ (5 / 6 : Real) * (Q : Real) +
          Real.sqrt (X : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hmiddleScale :
      (X : Real) ^ (5 / 6 : Real) * (Q : Real) <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hxLastScale :
      (X : Real) + Real.sqrt (X : Real) * (Q : Real) ^ 2 <=
        vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  apply vaughanMean_le_of_cutoff_bounds u X Q
  · simpa [u] using middleLevelCutoff_one_le X hX
  · simpa [u] using middleLevelCutoff_le X hX
  · exact hX
  · exact hQ
  · exact (middleLevelSmallTerm_le hxReal hqReal hqCubeXReal huRoot).trans
      hmiddleLastScale
  · exact (middleLevelInverseTerm_le hxReal hqReal hrootU).trans hmiddleScale
  · exact (middleLevelForwardTerm_le hxReal hqReal huRoot).trans hmiddleLastScale
  · exact (middleLevelShortTerm_le hxReal hqReal hqCubeXReal huRoot).trans hxLastScale

end BombieriVinogradov.VaughanMeanValue
