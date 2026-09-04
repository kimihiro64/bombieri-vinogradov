import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveDifference
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Pointwise weight of the imprimitive character correction

The correction vanishes at integers coprime to the ambient level. Elsewhere
its norm is at most the underlying von Mangoldt weight.
-/
set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem norm_mangoldt_mul_natCast_sub_primitive_le
    {N : Nat} (chi : _root_.DirichletCharacter Complex N) (n : Nat) :
    norm ((ArithmeticFunction.vonMangoldt n : Complex) *
      (chi (n : ZMod N) - chi.primitiveCharacter (n : ZMod chi.conductor))) <=
        if Nat.Coprime n N then 0 else ArithmeticFunction.vonMangoldt n := by
  rw [natCast_sub_primitiveCharacter_eq]
  by_cases h : Nat.Coprime n N
  case pos =>
    rw [if_pos h, if_pos h]
    simp only [mul_zero, norm_zero, le_refl]
  case neg =>
    simp only [h, if_false]
    rw [norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (chi.primitiveCharacter.norm_le_one n)

end BombieriVinogradov.DirichletCharacter
