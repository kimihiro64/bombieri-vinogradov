import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegral
import BombieriVinogradov.Helpers.DirichletCharacter.CpowDerivative

/-!
# Normalization of the character Abel integral

This module owns the exact conversion from the differentiated Abel-summation
integral to the source form `s * integral A(t) t^(-s-1) dt`.
-/

set_option autoImplicit false

open Finset MeasureTheory Set

namespace BombieriVinogradov

/-- The derivative-form Abel integral equals the source-normalized character integral. -/
theorem neg_integral_deriv_cpow_mul_characterPartialSum_eq_abelIntegral
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    -(∫ t in Ioi (1 : ℝ), deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, chi k) = characterAbelIntegral chi s := by
  rw [characterAbelIntegral, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Complex.deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne',
    sum_character_Icc_zero_eq_one chi hchi]
  · ring_nf
  · exact neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs)

end BombieriVinogradov
