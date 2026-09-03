import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quadratic absorption into a logarithmic endpoint scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.RealAnalysis

theorem log_nat_add_two_sq_le_four_mul_endpoint_sq
    {N K : Nat} (hN : 3 <= N) (hK : 1 <= K) :
    (Real.log N + 2) ^ 2 <=
      4 * (Real.log N + Real.log ((K : Real) + 2)) ^ 2 := by
  have hOneLeLogThree : (1 : Real) <= Real.log 3 := by
    have h := Real.le_log_one_add_of_nonneg
      (x := (2 : Real)) (by norm_num)
    norm_num at h
    exact h
  have hThreeLeN : (3 : Real) <= (N : Real) := (Nat.cast_le).2 hN
  have hOneLeLogN : (1 : Real) <= Real.log N :=
    hOneLeLogThree.trans (Real.log_le_log (by norm_num) hThreeLeN)
  have hThreeNat : 3 <= K + 2 := by
    have h := Nat.add_le_add_right hK 2
    norm_num at h
    exact h
  have hThreeCast : (3 : Real) <= ((K + 2 : Nat) : Real) :=
    (Nat.cast_le).2 hThreeNat
  have hThreeLeKAddTwo : (3 : Real) <= (K : Real) + 2 := by
    norm_num at hThreeCast
    exact hThreeCast
  have hOneLeLogKAddTwo :
      (1 : Real) <= Real.log ((K : Real) + 2) :=
    hOneLeLogThree.trans
      (Real.log_le_log (by norm_num) hThreeLeKAddTwo)
  have hLeftNonneg : 0 <= Real.log N + 2 := by
    linarith
  have hLinear :
      Real.log N + 2 <=
        2 * (Real.log N + Real.log ((K : Real) + 2)) := by
    linarith
  have hNeg :
      -(2 * (Real.log N + Real.log ((K : Real) + 2))) <=
        Real.log N + 2 := by
    linarith
  have hSquare := sq_le_sq' hNeg hLinear
  calc
    (Real.log N + 2) ^ 2 <=
        (2 * (Real.log N + Real.log ((K : Real) + 2))) ^ 2 := hSquare
    _ = 4 * (Real.log N + Real.log ((K : Real) + 2)) ^ 2 := by
      ring

end BombieriVinogradov.RealAnalysis
