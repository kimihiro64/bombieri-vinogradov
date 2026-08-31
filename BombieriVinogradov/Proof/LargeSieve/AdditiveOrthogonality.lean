import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Additive orthogonality and Parseval on `ZMod q`

This module contains the finite additive Fourier calculation used to turn
primitive multiplicative character sums into sums at reduced rational points.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- Complex conjugation of the standard additive character negates its input. -/
theorem star_stdAddChar_apply {q : Nat} [NeZero q] (x : ZMod q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hq : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne q)
  simpa only [RCLike.star_def, AddChar.inv_apply] using
    (AddChar.starComp_apply hq (φ := ZMod.stdAddChar) x)

/-- Orthogonality of the standard additive character on `ZMod q`. -/
theorem stdAddCharOrthogonality {q : Nat} [NeZero q] (x y : ZMod q) :
    (∑ a : ZMod q,
        star (ZMod.stdAddChar (x * a)) * ZMod.stdAddChar (y * a)) =
      if x = y then (q : Complex) else 0 := by
  have rearrange (a : ZMod q) : -(x * a) + y * a = a * (y - x) := by
    ring
  simp_rw [star_stdAddChar_apply, ← AddChar.map_add_eq_mul, rearrange]
  simpa [sub_eq_zero, eq_comm] using
    (AddChar.sum_mulShift (R := ZMod q) (R' := Complex) (y - x)
      (ZMod.isPrimitive_stdAddChar q))

/-- The finite Fourier transform attached to the standard additive character. -/
def additiveTransform {q : Nat} [NeZero q] (f : ZMod q -> Complex)
    (a : ZMod q) : Complex :=
  ∑ x, f x * ZMod.stdAddChar (x * a)

/-- Complex-valued additive Parseval identity on `ZMod q`. -/
theorem additiveParseval {q : Nat} [NeZero q] (f : ZMod q -> Complex) :
    (∑ a : ZMod q, star (additiveTransform f a) * additiveTransform f a) =
      (q : Complex) * ∑ x, star (f x) * f x := by
  classical
  unfold additiveTransform
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  have rearrange (a x y : ZMod q) :
      star (ZMod.stdAddChar (x * a)) * star (f x) *
          (f y * ZMod.stdAddChar (y * a)) =
        (star (f x) * f y) *
          (star (ZMod.stdAddChar (x * a)) * ZMod.stdAddChar (y * a)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [stdAddCharOrthogonality]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring

/-- Real norm-squared additive Parseval identity on `ZMod q`. -/
theorem additiveParseval_normSq {q : Nat} [NeZero q]
    (f : ZMod q -> Complex) :
    (∑ a : ZMod q, ‖additiveTransform f a‖ ^ 2) =
      (q : Real) * ∑ x, ‖f x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using
    (additiveParseval f)

end BombieriVinogradov.LargeSieve
