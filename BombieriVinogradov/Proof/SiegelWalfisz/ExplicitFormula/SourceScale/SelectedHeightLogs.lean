import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Selected-height logarithms versus the source logarithm
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem abs_log_level_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x) :
    abs (Real.log N) <= Real.log ((N * x : Nat) : Real) := by
  have hNOne : (1 : Real) <= (N : Real) :=
    (Nat.one_le_cast).mpr (le_trans (by norm_num) hN)
  rw [abs_of_nonneg (Real.log_nonneg hNOne)]
  exact log_level_le_log_level_mul_argument hN hx

theorem log_selectedHeight_add_two_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x)
    {T Tprime : Real} (hT : 2 <= T)
    (hLower : T <= Tprime) (hUpper : Tprime <= T + 1)
    (hTx : T <= x) :
    Real.log (Tprime + 2) <=
      Real.log ((N * x : Nat) : Real) := by
  have hLocal :
      Real.log (Tprime + 2) <= Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  exact hLocal.trans
    (log_height_add_three_le_log_level_mul_argument hN hx hT hTx)

theorem log_selectedHeight_add_one_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x)
    {T Tprime : Real} (hT : 2 <= T)
    (hLower : T <= Tprime) (hUpper : Tprime <= T + 1)
    (hTx : T <= x) :
    Real.log (Tprime + 1) <=
      Real.log ((N * x : Nat) : Real) := by
  have hLocal :
      Real.log (Tprime + 1) <= Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  exact hLocal.trans
    (log_height_add_three_le_log_level_mul_argument hN hx hT hTx)

end BombieriVinogradov.SiegelWalfisz
