import BombieriVinogradov.Helpers.DirichletCharacter.FiniteWeightedOrthogonality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Exact principal-character separation

The principal character is removed from the finite Fourier expansion
before estimating the centered discrepancy.
-/
set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem totient_mul_residue_eq_nonprincipal_add_principal
    {N : Nat} [NeZero N] (a : Units (ZMod N))
    (s : Finset Nat) (f : Nat -> Complex) :
    (N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) =
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N))) +
        Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N)) := by
  have hOne : (1 : _root_.DirichletCharacter Complex N)
      (Inv.inv (a : ZMod N)) = 1 := by
    rw [ZMod.inv_coe_unit]
    exact MulChar.one_apply_coe (Inv.inv a)
  have hSplit := Finset.sum_erase_add
    (Finset.univ : Finset (_root_.DirichletCharacter Complex N))
    (fun chi => chi (Inv.inv (a : ZMod N)) *
      Finset.sum s (fun n => f n * chi (n : ZMod N)))
    (Finset.mem_univ (1 : _root_.DirichletCharacter Complex N))
  rw [hOne, one_mul, sum_characters_weighted_eq_totient_mul_residue] at hSplit
  exact hSplit.symm

end BombieriVinogradov.DirichletCharacter
