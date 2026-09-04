import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Exact number of nonprincipal complex characters

Removing the principal character leaves exactly one fewer than
the totient, including the single-character level-one case.
-/
set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem card_nonprincipal_add_one_eq_totient {N : Nat} [NeZero N] :
    (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N)).card + 1 = N.totient := by
  have hCard := Finset.card_erase_add_one
    (Finset.mem_univ (1 : _root_.DirichletCharacter Complex N))
  rw [Finset.card_univ, <- Nat.card_eq_fintype_card,
    _root_.DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity Complex N] at hCard
  exact hCard

end BombieriVinogradov.DirichletCharacter
