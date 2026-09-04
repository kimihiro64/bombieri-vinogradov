import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Helpers.DirichletCharacter.NonprincipalCard
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Cardinality of primitive nonprincipal characters

The primitive nonprincipal characters form a subset of all nonprincipal
characters, so their cardinality is bounded by the modulus totient.
-/

set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

/-- A positive modulus has at most phi(N) primitive nonprincipal characters. -/
theorem card_primitive_nonprincipal_le_totient {N : Nat} [NeZero N] :
    ((LargeSieve.primitiveCharacters N).erase 1).card <= N.totient := by
  calc
    ((LargeSieve.primitiveCharacters N).erase 1).card <=
        (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N)).card :=
      Finset.card_le_card (Finset.erase_subset_erase 1
        (Finset.subset_univ (LargeSieve.primitiveCharacters N)))
    _ <= (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N)).card + 1 :=
      Nat.le_succ _
    _ = N.totient := card_nonprincipal_add_one_eq_totient

end BombieriVinogradov.DirichletCharacter
