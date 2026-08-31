import BombieriVinogradov.Proof.LargeSieve.AdditiveOrthogonality
import BombieriVinogradov.Proof.LargeSieve.CharacterOrthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Primitive Dirichlet-character Gauss sums

The key result is the composite-modulus identity `|tau(chi)|^2 = q` for a
primitive complex Dirichlet character modulo `q`.  The proof uses additive
Parseval and Mathlib's primitive Gauss-shift formula; it does not replace the
composite residue ring by a field.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- The squared complex character values over all residues have total mass `phi(q)`. -/
theorem dirichletCharacterEnergy {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) :
    (∑ x : ZMod q, star (chi x) * chi x) = (q.totient : Complex) := by
  calc
    _ = ∑ x : ZMod q, (star chi * chi) x := by
      simp only [MulChar.star_apply, MulChar.mul_apply]
    _ = ∑ x : ZMod q, (1 : DirichletCharacter Complex q) x := by
      rw [MulChar.star_eq_inv]
      simp
    _ = _ := by
      rw [MulChar.sum_one_eq_card_units]
      norm_cast
      exact ZMod.card_units_eq_totient q

/-- Parseval energy of all additive shifts of a Dirichlet-character Gauss sum. -/
theorem gaussSumShiftParseval {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) :
    (∑ a : ZMod q,
        star (gaussSum chi ((ZMod.stdAddChar).mulShift a)) *
          gaussSum chi ((ZMod.stdAddChar).mulShift a)) =
      (q : Complex) * (q.totient : Complex) := by
  calc
    _ = ∑ a : ZMod q,
        star (additiveTransform (fun x => chi x) a) *
          additiveTransform (fun x => chi x) a := by
      simp only [additiveTransform, gaussSum, AddChar.mulShift_apply, mul_comm]
    _ = (q : Complex) * ∑ x : ZMod q, star (chi x) * chi x :=
      additiveParseval (fun x => chi x)
    _ = _ := by rw [dirichletCharacterEnergy]

/-- For primitive `chi`, every shifted Gauss sum is a character multiple of `tau(chi)`. -/
theorem gaussSumShiftEnergy_of_isPrimitive {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    (∑ a : ZMod q,
        star (gaussSum chi ((ZMod.stdAddChar).mulShift a)) *
          gaussSum chi ((ZMod.stdAddChar).mulShift a)) =
      (q.totient : Complex) *
        (star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar) := by
  simp_rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hchi]
  simp_rw [star_mul]
  have rearrange (a : ZMod q) :
      star (gaussSum chi ZMod.stdAddChar) * star (chi⁻¹ a) *
          (chi⁻¹ a * gaussSum chi ZMod.stdAddChar) =
        (star (chi⁻¹ a) * chi⁻¹ a) *
          (star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar) := by
    ring
  simp_rw [rearrange]
  rw [← Finset.sum_mul]
  rw [dirichletCharacterEnergy (chi := chi⁻¹)]

/-- Complex self-product form of the primitive Gauss-sum norm identity. -/
theorem gaussSum_star_mul_self_of_isPrimitive {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar =
      (q : Complex) := by
  have htotient : (q.totient : Complex) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply mul_left_cancel₀ htotient
  calc
    (q.totient : Complex) *
        (star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar) =
      ∑ a : ZMod q,
        star (gaussSum chi ((ZMod.stdAddChar).mulShift a)) *
          gaussSum chi ((ZMod.stdAddChar).mulShift a) :=
      (gaussSumShiftEnergy_of_isPrimitive hchi).symm
    _ = (q : Complex) * (q.totient : Complex) := gaussSumShiftParseval chi
    _ = (q.totient : Complex) * (q : Complex) := by ring

/-- For primitive `chi mod q`, the squared norm of its standard Gauss sum is `q`. -/
theorem normSq_gaussSum_stdAddChar {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    Complex.normSq (gaussSum chi ZMod.stdAddChar) = (q : Real) := by
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  simpa only [RCLike.star_def] using gaussSum_star_mul_self_of_isPrimitive hchi

/-- Norm notation for the primitive Gauss-sum identity. -/
theorem norm_gaussSum_stdAddChar_sq {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 = (q : Real) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact normSq_gaussSum_stdAddChar hchi

end BombieriVinogradov.LargeSieve
