import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Nonvanishing of one level-correction factor

A prime Euler factor removed when passing to the inducing primitive character
cannot vanish in the open right half-plane.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_prime_cpow_lt_one_of_re_pos {p : Nat} (hp : p.Prime)
    {s : Complex} (hs : 0 < s.re) :
    ‖(p : Complex) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by
    rw [Complex.neg_re]
    linarith)]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hp.one_lt
  · rw [Complex.neg_re]
    linarith

theorem levelCorrectionFactor_ne_zero_of_re_pos {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) {p : Nat} (hp : p.Prime)
    {s : Complex} (hs : 0 < s.re) :
    levelCorrectionFactor chi p s ≠ 0 := by
  have hPower := norm_prime_cpow_lt_one_of_re_pos hp hs
  have hCharacter : ‖chi.primitiveCharacter p‖ ≤ 1 :=
    _root_.DirichletCharacter.norm_le_one chi.primitiveCharacter p
  have hProduct :
      ‖chi.primitiveCharacter p * (p : Complex) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖chi.primitiveCharacter p‖ * ‖(p : Complex) ^ (-s)‖ ≤
          1 * ‖(p : Complex) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right hCharacter (norm_nonneg _)
      _ < 1 * 1 := mul_lt_mul_of_pos_left hPower zero_lt_one
      _ = 1 := one_mul 1
  rw [levelCorrectionFactor]
  apply sub_ne_zero.mpr
  intro hOne
  rw [← hOne] at hProduct
  norm_num at hProduct

end BombieriVinogradov.SiegelWalfisz
