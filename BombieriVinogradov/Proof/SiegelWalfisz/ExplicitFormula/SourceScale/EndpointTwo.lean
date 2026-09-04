import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Logarithmic source-scale comparisons at x=2

The primary scale absorbs constants, and the height-two reciprocal-zero
bound has at most four times the same squared logarithm.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem endpointTwo_sourceLog_bounds {N : Nat} (hN : 3 <= N) :
    And (1 <= (Real.log ((N * 2 : Nat) : Real)) ^ 2)
      ((Real.log N + Real.log 4) ^ 2 <=
        4 * (Real.log ((N * 2 : Nat) : Real)) ^ 2) := by
  let L := Real.log ((N * 2 : Nat) : Real)
  have hOne : 1 <= L := one_le_log_natCast (x := N * 2) (by omega)
  have hSquare : 0 <= (L - 1) ^ 2 := sq_nonneg (L - 1)
  have hSquareOne : 1 <= L ^ 2 := by nlinarith
  have hNPos : 0 < (N : Real) := Nat.cast_pos.mpr (by omega)
  have hNLe : (N : Real) <= ((N * 2 : Nat) : Real) :=
    (Nat.cast_le).2 (show N <= N * 2 by omega)
  have hFourLe : (4 : Real) <= ((N * 2 : Nat) : Real) :=
    (Nat.cast_le).2 (show 4 <= N * 2 by omega)
  have hLogN : Real.log N <= L := Real.log_le_log hNPos hNLe
  have hLogFour : Real.log 4 <= L :=
    Real.log_le_log (by norm_num) hFourLe
  have hNonneg : 0 <= Real.log N + Real.log 4 := by positivity
  have hProduct : 0 <=
      (2 * L - (Real.log N + Real.log 4)) *
        (2 * L + (Real.log N + Real.log 4)) :=
    mul_nonneg (by linarith) (by linarith)
  exact And.intro hSquareOne (by nlinarith)

end BombieriVinogradov.SiegelWalfisz
