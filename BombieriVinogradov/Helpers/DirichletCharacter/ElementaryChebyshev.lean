import BombieriVinogradov.Definitions.VaughanMeanValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Order.Interval.Finset.Nat

/-!
# Elementary character Chebyshev bound

The triangle inequality, the unit character bound and the termwise
Mangoldt logarithm bound control every finite endpoint.
-/
set_option autoImplicit false

namespace BombieriVinogradov.VaughanMeanValue

theorem norm_psiCharacterSum_le_mul_log
    {N : Nat} (chi : _root_.DirichletCharacter Complex N) (x : Nat) :
    norm (psiCharacterSum x N chi) <= (x : Real) * Real.log x := by
  unfold psiCharacterSum
  calc
    norm (Finset.sum (Finset.Icc 1 x) (fun n =>
        (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N))) <=
        Finset.sum (Finset.Icc 1 x) (fun _ => Real.log x) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      have hBounds := Finset.mem_Icc.mp hn
      have hnPos : (0 : Real) < (n : Real) :=
        Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hBounds.1)
      have hnLe : (n : Real) <= (x : Real) := Nat.cast_le.mpr hBounds.2
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (chi.norm_le_one n)).trans
          (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnPos hnLe))
    _ = (x : Real) * Real.log x := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

end BombieriVinogradov.VaughanMeanValue
