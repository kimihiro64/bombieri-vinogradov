import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Nonvanishing of principal level-correction factors

This module proves that the finite Euler product attached to a principal
Dirichlet character is nonzero on the positive real axis.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem principalLevelCorrection_ne_zero {N : ℕ} [NeZero N]
    {t : ℝ} (ht : 0 < t) :
    Ne (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-(t : ℂ)))) 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  apply sub_ne_zero.mpr
  intro hone
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hnorm : ‖(p : ℂ) ^ (-(t : ℂ))‖ = (p : ℝ) ^ (-t) := by
    rw [← Complex.ofReal_natCast p,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    norm_num
  have hrpowLt : (p : ℝ) ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpgt (neg_neg_of_pos ht)
  have honeNorm := congrArg norm hone
  rw [norm_one, hnorm] at honeNorm
  linarith

end BombieriVinogradov.SiegelWalfisz
