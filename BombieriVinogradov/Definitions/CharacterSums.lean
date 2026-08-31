import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Character sums for the large-sieve route

This module fixes the exact source-level objects used in Vaughan's character
large-sieve theorem.  Proofs live under `Proof/LargeSieve` so that changes to
the analytic argument do not destabilize the project-wide statement surface.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- The finite set of primitive complex Dirichlet characters of level `q`. -/
def primitiveCharacters (q : Nat) : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter DirichletCharacter.IsPrimitive

/-- The interval character sum `S(chi)` in Vaughan's Theorem 4. -/
def intervalCharacterSum (a : Int -> Complex) (M : Int) (N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)), a n * chi (n : ZMod q)

/-- A character transform of a function on the unit group of `ZMod q`. -/
def unitCharacterSum {q : Nat} (a : (ZMod q)ˣ -> Complex)
    (chi : DirichletCharacter Complex q) : Complex := by
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  exact ∑ x, a x * chi (x : ZMod q)

/--
The source-faithful asymptotic statement of Vaughan's primitive-character
large sieve.  The existential constant is absolute: it precedes every
interval, length, level, and coefficient sequence.
-/
def CharacterLargeSieveStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧
      ∀ (M : Int) (N Q : Nat) (a : Int -> Complex), 1 <= Q ->
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
            ∑ chi ∈ primitiveCharacters q,
              ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
          C * ((N : Real) + (Q : Real) ^ 2) *
            ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2

end BombieriVinogradov.LargeSieve
