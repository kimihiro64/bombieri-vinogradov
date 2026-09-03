import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Basic comparisons with the source logarithm

This module proves the elementary argument inequalities placing every
logarithm used by the contour estimates below log(N*x).
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem one_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x) :
    (1 : Real) <= Real.log ((N * x : Nat) : Real) := by
  have hNine : 3 * 3 <= N * x :=
    Nat.mul_le_mul hN (Nat.succ_le_iff.mpr hx)
  exact one_le_log_natCast
    (lt_of_lt_of_le (by norm_num) hNine)

theorem log_level_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x) :
    Real.log N <= Real.log ((N * x : Nat) : Real) := by
  have hxOne : 1 <= x :=
    le_trans (by norm_num) (Nat.le_of_lt hx)
  have hNat : N <= N * x := by
    calc
      N = N * 1 := by simp
      _ <= N * x := Nat.mul_le_mul_left N hxOne
  have hNPos : 0 < (N : Real) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) hN)
  exact Real.log_le_log hNPos ((Nat.cast_le).2 hNat)

theorem log_argument_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x) :
    Real.log x <= Real.log ((N * x : Nat) : Real) := by
  have hNOne : 1 <= N := le_trans (by norm_num) hN
  have hNat : x <= N * x := by
    calc
      x = 1 * x := by simp
      _ <= N * x := Nat.mul_le_mul_right x hNOne
  have hxPos : 0 < (x : Real) :=
    Nat.cast_pos.mpr (lt_trans (by norm_num) hx)
  exact Real.log_le_log hxPos ((Nat.cast_le).2 hNat)

theorem log_two_mul_argument_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x) :
    Real.log (2 * (x : Real)) <=
      Real.log ((N * x : Nat) : Real) := by
  have hTwoLeN : 2 <= N := le_trans (by norm_num) hN
  have hTwoLeNReal : (2 : Real) <= (N : Real) :=
    (Nat.cast_le).2 hTwoLeN
  have hArgLe :
      (2 : Real) * (x : Real) <= (N : Real) * (x : Real) :=
    mul_le_mul_of_nonneg_right hTwoLeNReal (Nat.cast_nonneg x)
  have hArgPos : 0 < (2 : Real) * (x : Real) :=
    mul_pos (by norm_num)
      (Nat.cast_pos.mpr (lt_trans (by norm_num) hx))
  apply Real.log_le_log hArgPos
  simpa only [Nat.cast_mul] using hArgLe

theorem log_height_add_three_le_log_level_mul_argument
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    Real.log (T + 3) <= Real.log ((N * x : Nat) : Real) := by
  have hxThree : (3 : Real) <= (x : Real) := by
    exact (Nat.cast_le).2 (Nat.succ_le_iff.mpr hx)
  have hTThreeLeTwoX : T + 3 <= 2 * (x : Real) := by
    linarith
  have hTwoLeNReal : (2 : Real) <= (N : Real) := by
    exact (Nat.cast_le).2 (le_trans (by norm_num) hN)
  have hTwoXLeNX :
      2 * (x : Real) <= (N : Real) * (x : Real) :=
    mul_le_mul_of_nonneg_right hTwoLeNReal (Nat.cast_nonneg x)
  have hArgLe : T + 3 <= ((N * x : Nat) : Real) := by
    rw [Nat.cast_mul]
    exact hTThreeLeTwoX.trans hTwoXLeNX
  exact Real.log_le_log (by linarith) hArgLe

end BombieriVinogradov.SiegelWalfisz
