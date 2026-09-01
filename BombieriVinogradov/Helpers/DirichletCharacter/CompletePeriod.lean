import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Complete-period Dirichlet-character cancellation

This module owns the identification of one natural residue block with `ZMod N`
and the resulting vanishing sum for a nonprincipal complex character.
-/

set_option autoImplicit false

open Finset

namespace BombieriVinogradov

/-- A nonprincipal complex Dirichlet character sums to zero over one complete natural period. -/
theorem sum_character_range_modulus_eq_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ∑ n ∈ range N, chi n = 0 := by
  calc
    ∑ n ∈ range N, chi n = ∑ a : ZMod N, chi a := by
      refine Finset.sum_bij (s := range N) (t := univ)
        (f := fun n : ℕ => chi n) (g := fun a : ZMod N => chi a)
        (fun n _hn => (n : ZMod N)) ?_ ?_ ?_ ?_
      · intro n hn
        simp
      · intro a ha b hb hab
        have hval := congrArg ZMod.val hab
        simpa [ZMod.val_natCast_of_lt (mem_range.mp ha),
          ZMod.val_natCast_of_lt (mem_range.mp hb)] using hval
      · intro a ha
        exact ⟨a.val, mem_range.mpr a.val_lt, a.natCast_zmod_val⟩
      · intro n hn
        rfl
    _ = 0 := chi.sum_eq_zero_of_ne_one hchi

end BombieriVinogradov
