import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.TrigonometricWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Pointwise Euler weight for logarithmic-derivative positivity

This module packages the nonnegative von Mangoldt weight arising from the
three-term de la Vallee Poussin combination at one natural-number index.
-/

set_option autoImplicit false

open ArithmeticFunction hiding log

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def zeroFreeEulerWeight {N : ℕ}
    (chi : DirichletCharacter ℂ N) (sigma t : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if n = 0 then 0
    else if IsUnit (n : ZMod N) then
      Λ n * (n : ℝ) ^ (-sigma) *
        (3 + 4 * (chi n * (n : ℂ) ^ (-(Complex.I * t))) +
          (chi n * (n : ℂ) ^ (-(Complex.I * t))) ^ 2).re
    else 0

theorem zeroFreeEulerWeight_nonneg {N : ℕ}
    (chi : DirichletCharacter ℂ N) (sigma t : ℝ) (n : ℕ) :
    0 ≤ zeroFreeEulerWeight chi sigma t n := by
  classical
  rw [zeroFreeEulerWeight]
  split_ifs with hn hunit
  · exact le_rfl
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hz :
        ‖chi n * (n : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
      rw [norm_mul, ← hunit.unit_spec,
        DirichletCharacter.unit_norm_eq_one chi hunit.unit,
        ← Complex.ofReal_natCast n,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hnPos)]
      have hexponent : (-(Complex.I * (t : ℂ))).re = 0 := by
        norm_num [Complex.mul_re]
      rw [hexponent, Real.rpow_zero]
      norm_num
    exact mul_nonneg
      (mul_nonneg vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-sigma)))
      (re_three_add_four_mul_add_sq_nonneg hz)
  · exact le_rfl

end BombieriVinogradov.SiegelWalfisz
