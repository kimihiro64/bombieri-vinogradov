import BombieriVinogradov.Definitions.CharacterSums
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Character orthogonality and Parseval

This file isolates the exact finite Fourier calculation used in the
multiplicative large-sieve route.  It deliberately sums over the unit group,
where conjugating a character value is the same as evaluating at the inverse.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

noncomputable local instance unitFintype (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- A nonnegative sum over primitive characters is bounded by the sum over all characters. -/
theorem primitiveSum_le_all (q : Nat) (f : DirichletCharacter Complex q -> Real)
    (hf : ∀ chi, 0 <= f chi) :
    ∑ chi ∈ primitiveCharacters q, f chi <= ∑ chi, f chi := by
  classical
  exact Finset.sum_le_univ_sum_of_nonneg (s := primitiveCharacters q) hf

/-- On units, complex conjugation of a character value is evaluation at the inverse. -/
theorem star_character_apply_unit {q : Nat} (chi : DirichletCharacter Complex q)
    (x : (ZMod q)ˣ) :
    star (chi (x : ZMod q)) = chi ((x : ZMod q)⁻¹) := by
  rw [MulChar.star_apply']
  rw [MulChar.inv_apply_eq_inv']
  simp

/-- Orthogonality of all complex Dirichlet characters on the unit group. -/
theorem characterOrthogonalityOnUnits {q : Nat} [NeZero q]
    (x y : (ZMod q)ˣ) :
    (∑ chi : DirichletCharacter Complex q,
        star (chi (x : ZMod q)) * chi (y : ZMod q)) =
      if x = y then (q.totient : Complex) else 0 := by
  simp_rw [star_character_apply_unit]
  simpa only [Units.val_inj] using
    (DirichletCharacter.sum_char_inv_mul_char_eq (R := Complex)
      x.isUnit (y : ZMod q))

/-- Finite Parseval identity for the Dirichlet-character transform on `(ZMod q)^*`. -/
theorem characterParseval {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q,
        star (unitCharacterSum a chi) * unitCharacterSum a chi) =
      (q.totient : Complex) * ∑ x, star (a x) * a x := by
  classical
  unfold unitCharacterSum
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, y]
    rw [Finset.sum_comm]
  have rearrange (chi : DirichletCharacter Complex q) (x y : (ZMod q)ˣ) :
      star (chi (x : ZMod q)) * star (a x) *
          (a y * chi (y : ZMod q)) =
        (star (a x) * a y) *
          (star (chi (x : ZMod q)) * chi (y : ZMod q)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [characterOrthogonalityOnUnits]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring

/-- Real norm-squared form of character Parseval, ready for analytic inequalities. -/
theorem characterParseval_normSq {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q, ‖unitCharacterSum a chi‖ ^ 2) =
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using
    (characterParseval a)

/--
Discarding imprimitive characters gives the fixed-modulus primitive-character
bound that feeds the large-sieve argument.
-/
theorem primitiveCharacterParseval_le {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum a chi‖ ^ 2 <=
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  calc
    _ <= ∑ chi : DirichletCharacter Complex q,
        ‖unitCharacterSum a chi‖ ^ 2 :=
      primitiveSum_le_all q _ (fun chi => sq_nonneg ‖unitCharacterSum a chi‖)
    _ = _ := characterParseval_normSq a

end BombieriVinogradov.LargeSieve
