import BombieriVinogradov.Helpers.DirichletCharacter.FinitePrincipalSeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic.Ring

/-!
# Centered finite residue discrepancy bound

Only nonprincipal character sums remain after principal separation.
The exact global-minus-principal correction is retained explicitly.
-/
set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem norm_totient_mul_residue_sub_sum_le
    {N : Nat} [NeZero N] (a : Units (ZMod N))
    (s : Finset Nat) (f : Nat -> Complex) :
    norm ((N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) -
          Finset.sum s f) <=
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (Finset.sum s (fun n => f n * chi (n : ZMod N)))) +
      norm (Finset.sum s f - Finset.sum s (fun n => f n *
        (1 : _root_.DirichletCharacter Complex N) (n : ZMod N))) := by
  have hRest :
      norm (Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N)))) <=
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (Finset.sum s (fun n => f n * chi (n : ZMod N)))) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro chi _hchi
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (chi.norm_le_one (Inv.inv (a : ZMod N)))
  calc
    norm ((N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) -
          Finset.sum s f) =
      norm (Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N))) -
        (Finset.sum s f - Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N)))) := by
      rw [totient_mul_residue_eq_nonprincipal_add_principal]
      congr 1
      ring
    _ <= norm (Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N)))) +
        norm (Finset.sum s f - Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N))) := norm_sub_le _ _
    _ <= Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (Finset.sum s (fun n => f n * chi (n : ZMod N)))) +
        norm (Finset.sum s f - Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N))) :=
      add_le_add hRest (le_refl _)

end BombieriVinogradov.DirichletCharacter
