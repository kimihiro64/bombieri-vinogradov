import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Retained cutoff logarithms versus the source scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem log_level_add_log_ceil_add_two_sq_le_four_mul_sourceLog_sq
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 <=
      4 * (Real.log ((N * x : Nat) : Real)) ^ 2 := by
  let L := Real.log ((N * x : Nat) : Real)
  have hLOne : 1 <= L := by
    simpa [L] using one_le_log_level_mul_argument hN hx
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hLogNLe : Real.log N <= L := by
    simpa [L] using log_level_le_log_level_mul_argument hN hx
  have hTNonneg : 0 <= T := le_trans (by norm_num) hT
  have hCeilLt : ((Nat.ceil T : Nat) : Real) < T + 1 :=
    Nat.ceil_lt_add_one hTNonneg
  have hCeilAddTwoLe :
      ((Nat.ceil T : Nat) : Real) + 2 <= T + 3 := by
    linarith
  have hCeilArgPos :
      0 < ((Nat.ceil T : Nat) : Real) + 2 := by
    have hCeilNonneg : 0 <= ((Nat.ceil T : Nat) : Real) :=
      Nat.cast_nonneg (Nat.ceil T)
    linarith
  have hLogCeilLeHeight :
      Real.log (((Nat.ceil T : Nat) : Real) + 2) <= Real.log (T + 3) :=
    Real.log_le_log hCeilArgPos hCeilAddTwoLe
  have hLogHeightLe : Real.log (T + 3) <= L := by
    simpa [L] using log_height_add_three_le_log_level_mul_argument
      hN hx hT hTx
  have hLogCeilLe :
      Real.log (((Nat.ceil T : Nat) : Real) + 2) <= L :=
    hLogCeilLeHeight.trans hLogHeightLe
  have hThreeNReal : (3 : Real) <= (N : Real) := (Nat.cast_le).2 hN
  have hLogNNonneg : 0 <= Real.log N :=
    Real.log_nonneg (by linarith)
  have hLogCeilNonneg :
      0 <= Real.log (((Nat.ceil T : Nat) : Real) + 2) :=
    Real.log_nonneg (by linarith)
  have hLinear :
      Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2) <= 2 * L := by
    linarith
  have hNeg :
      -(2 * L) <=
        Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2) := by
    linarith
  have hSquare := sq_le_sq' hNeg hLinear
  calc
    (Real.log N + Real.log (((Nat.ceil T : Nat) : Real) + 2)) ^ 2 <=
        (2 * L) ^ 2 := hSquare
    _ = 4 * (Real.log ((N * x : Nat) : Real)) ^ 2 := by
      dsimp [L]
      ring

end BombieriVinogradov.SiegelWalfisz
