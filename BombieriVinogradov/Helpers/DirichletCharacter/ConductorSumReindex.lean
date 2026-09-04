import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveLiftUniqueness
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Divisors

/-!
# Exact reindexing by primitive conductor

Each nonprincipal character is induced by exactly one primitive
nonprincipal character at a divisor of the ambient modulus.
-/
set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem sum_nonprincipal_eq_sum_primitive_conductors {N : Nat} [NeZero N]
    (F : (q : Nat) -> _root_.DirichletCharacter Complex q -> Real) :
    Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
      (fun chi => F chi.conductor chi.primitiveCharacter) =
    Finset.sum N.divisors (fun q =>
      Finset.sum ((LargeSieve.primitiveCharacters q).erase 1) (F q)) := by
  symm
  rw [Finset.sum_sigma']
  refine Finset.sum_bij
    (fun p hp => _root_.DirichletCharacter.changeLevel
      (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).1) p.2)
    ?mem ?inj ?surj ?weight
  case mem =>
    intro p hp
    have hChar := (Finset.mem_erase.mp (Finset.mem_sigma.mp hp).2).1
    apply Finset.mem_erase.mpr
    exact And.intro
      (fun h => hChar ((_root_.DirichletCharacter.changeLevel_eq_one_iff _).mp h))
      (Finset.mem_univ _)
  case inj =>
    intro p hp q hq h
    exact primitive_sigma_eq_of_lift_eq _ _ p.2 q.2
      (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hp).2).2).2
      (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hq).2).2).2 h
  case surj =>
    intro chi hchi
    exact Exists.intro (Sigma.mk chi.conductor chi.primitiveCharacter)
      (Exists.intro (Finset.mem_sigma.mpr (And.intro
        (Nat.mem_divisors.mpr (And.intro chi.conductor_dvd_level (NeZero.ne N)))
        (Finset.mem_erase.mpr (And.intro
          (primitiveCharacter_ne_one_of_ne_one chi (Finset.mem_erase.mp hchi).1)
          (Finset.mem_filter.mpr (And.intro (Finset.mem_univ _)
            chi.primitiveCharacter_isPrimitive)))))) chi.changeLevel_primitiveCharacter)
  case weight =>
    intro p hp
    exact (congrArg (fun z : Sigma (fun q : Nat => _root_.DirichletCharacter Complex q) =>
      F z.1 z.2) (primitiveCharacter_sigma_changeLevel_eq
        (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).1) p.2
        (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hp).2).2).2)).symm

end BombieriVinogradov.DirichletCharacter
