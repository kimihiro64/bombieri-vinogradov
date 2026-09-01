import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.Core
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.SmallLevelAlgebra
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.SmallLevelCutoff
import Mathlib.Tactic

/-!
# Vaughan estimate in the small-level regime

This module composes the exact cutoff `u = Q^2`, its natural feasibility, and
the pure real inequalities under `Q^6 <= X` with the common cutoff interface.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem vaughanMean_le_smallLevel
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) (hqSixthX : Q ^ 6 <= X) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  let u := smallLevelCutoff Q
  have hqReal : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  have hx0 : (0 : Real) <= (X : Real) := by positivity
  have hqSixthXReal : (Q : Real) ^ 6 <= (X : Real) := by exact_mod_cast hqSixthX
  have hxScale : (X : Real) <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
    linarith
  apply vaughanMean_le_of_cutoff_bounds u X Q
  · exact smallLevelCutoff_one_le Q hQ
  · exact smallLevelCutoff_le X Q hQ hqSixthX
  · exact hX
  · exact hQ
  · simpa [u, smallLevelCutoff, Nat.cast_pow] using
      (smallLevelSmallTerm_le hqReal hqSixthXReal).trans hxScale
  · calc
      (X : Real) * (Q : Real) / Real.sqrt (u : Real) = (X : Real) := by
        simpa [u, smallLevelCutoff, Nat.cast_pow] using
          (smallLevelInverseTerm_eq (x := (X : Real)) (q := (Q : Real)) hqReal)
      _ <= vaughanSourceScale X Q := hxScale
  · simpa [u, smallLevelCutoff, Nat.cast_pow] using
      (smallLevelForwardTerm_le hx0 hqReal hqSixthXReal).trans hxScale
  · simpa [u, smallLevelCutoff, Nat.cast_pow] using
      (smallLevelShortTerm_le hqReal hqSixthXReal).trans hxScale

end BombieriVinogradov.VaughanMeanValue
