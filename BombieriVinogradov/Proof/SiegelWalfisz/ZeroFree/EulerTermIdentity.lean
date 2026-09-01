import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.EulerWeight
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LogDerivativeSeries

/-!
# Identification of the three logarithmic-derivative terms

This module rewrites the three L-series terms in Strombergsson Lemma 11.2 as
the single nonnegative pointwise Euler weight.
-/

set_option autoImplicit false

open ArithmeticFunction hiding log
open Complex
open scoped LSeries.notation

namespace BombieriVinogradov.SiegelWalfisz

theorem natCast_cpow_neg_add_I_mul {n : ℕ} (hn : Ne n 0)
    (sigma t : ℝ) :
    (n : ℂ) ^ (-((sigma : ℂ) + Complex.I * t)) =
      (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
        (n : ℂ) ^ (-(Complex.I * t)) := by
  have hnComplex : Ne (n : ℂ) 0 := by exact_mod_cast hn
  rw [neg_add, cpow_add _ _ hnComplex]
  congr 1
  rw [← ofReal_neg, ← ofReal_natCast n,
    ← ofReal_cpow (Nat.cast_nonneg n) (-sigma)]

theorem natCast_cpow_neg_add_two_I_mul {n : ℕ} (hn : Ne n 0)
    (sigma t : ℝ) :
    (n : ℂ) ^ (-((sigma : ℂ) + 2 * Complex.I * t)) =
      (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
        ((n : ℂ) ^ (-(Complex.I * t))) ^ 2 := by
  have hnComplex : Ne (n : ℂ) 0 := by exact_mod_cast hn
  rw [neg_add, cpow_add _ _ hnComplex]
  congr 1
  · rw [← ofReal_neg, ← ofReal_natCast n,
      ← ofReal_cpow (Nat.cast_nonneg n) (-sigma)]
  · rw [show -(2 * Complex.I * (t : ℂ)) =
        (2 : ℕ) * (-(Complex.I * (t : ℂ))) by ring,
      cpow_nat_mul]

theorem logDerivativeEulerTerms_eq_weight {N : ℕ}
    (chi : DirichletCharacter ℂ N) (sigma t : ℝ) (n : ℕ) :
    3 * (LSeries.term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) sigma n).re +
        4 * (LSeries.term (↗chi * ↗Λ)
          ((sigma : ℂ) + Complex.I * t) n).re +
        (LSeries.term (↗(chi ^ 2) * ↗Λ)
          ((sigma : ℂ) + 2 * Complex.I * t) n).re =
      zeroFreeEulerWeight chi sigma t n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [zeroFreeEulerWeight]
  by_cases hunit : IsUnit (n : ZMod N)
  · simp only [LSeries.term_of_ne_zero hn, Pi.mul_apply,
      zeroFreeEulerWeight, hn, hunit, if_false, if_true,
      MulChar.one_apply hunit, one_mul, chi.pow_apply' two_ne_zero]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ← cpow_neg, ← cpow_neg, ← cpow_neg,
      natCast_cpow_neg_add_I_mul hn sigma t,
      natCast_cpow_neg_add_two_I_mul hn sigma t,
      show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by norm_num,
      ← ofReal_natCast n, ← ofReal_cpow (Nat.cast_nonneg n) (-sigma),
      ]
    norm_num [mul_re]
    simp only [pow_two, mul_re, mul_im]
    ring
  · have hchi : chi n = 0 := MulChar.map_nonunit chi hunit
    have hchiSquare : (chi ^ 2) n = 0 := by simp [chi.pow_apply' two_ne_zero, hchi]
    have hone : (1 : DirichletCharacter ℂ N) n = 0 :=
      MulChar.map_nonunit 1 hunit
    simp [zeroFreeEulerWeight, hn, hunit,
      hchi, hchiSquare, hone]

end BombieriVinogradov.SiegelWalfisz
