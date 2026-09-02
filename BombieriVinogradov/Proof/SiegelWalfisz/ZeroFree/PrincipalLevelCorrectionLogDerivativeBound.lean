import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimeDivisorLogSum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalLevelCorrectionEulerFactor

/-!
# Logarithmic derivative of the principal correction product

This module assembles the local Euler-factor estimates into the uniform
ambient-level cost `log N`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_principalLevelCorrection_eq_sum
    {N : Nat} {s : Complex} (hs : 1 ≤ s.re) :
    logDeriv (principalLevelCorrection N) s =
      ∑ p ∈ N.primeFactors,
        logDeriv (principalLevelCorrectionFactor p) s := by
  have hFactor : forall p, p ∈ N.primeFactors ->
      principalLevelCorrectionFactor p s ≠ 0 := by
    intro p hp
    have hNorm := one_half_le_norm_principalLevelCorrectionFactor
      (Nat.prime_of_mem_primeFactors hp) hs
    exact norm_pos_iff.mp ((by norm_num : (0 : Real) < 1 / 2).trans_le hNorm)
  change logDeriv
      (fun z : Complex =>
        ∏ p ∈ N.primeFactors, principalLevelCorrectionFactor p z) s = _
  exact logDeriv_prod hFactor (fun p hp =>
    differentiableAt_principalLevelCorrectionFactor
      (Nat.prime_of_mem_primeFactors hp) s)

theorem principalLevelCorrection_ne_zero
    {N : Nat} {s : Complex} (hs : 1 ≤ s.re) :
    principalLevelCorrection N s ≠ 0 := by
  rw [principalLevelCorrection]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hNorm := one_half_le_norm_principalLevelCorrectionFactor
    (Nat.prime_of_mem_primeFactors hp) hs
  exact norm_pos_iff.mp ((by norm_num : (0 : Real) < 1 / 2).trans_le hNorm)

theorem differentiableAt_principalLevelCorrection
    {N : Nat} (s : Complex) :
    DifferentiableAt Complex (principalLevelCorrection N) s := by
  change DifferentiableAt Complex
    (fun z : Complex =>
      ∏ p ∈ N.primeFactors, principalLevelCorrectionFactor p z) s
  exact DifferentiableAt.fun_finsetProd (fun p hp =>
    differentiableAt_principalLevelCorrectionFactor
      (Nat.prime_of_mem_primeFactors hp) s)

theorem norm_logDeriv_principalLevelCorrection_le_log
    {N : Nat} [NeZero N] {s : Complex} (hs : 1 ≤ s.re) :
    ‖logDeriv (principalLevelCorrection N) s‖ ≤ Real.log N := by
  rw [logDeriv_principalLevelCorrection_eq_sum hs]
  calc
    ‖∑ p ∈ N.primeFactors,
        logDeriv (principalLevelCorrectionFactor p) s‖ ≤
        ∑ p ∈ N.primeFactors,
          ‖logDeriv (principalLevelCorrectionFactor p) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ N.primeFactors, Real.log p :=
      Finset.sum_le_sum (fun p hp =>
        norm_logDeriv_principalLevelCorrectionFactor_le_log
          (Nat.prime_of_mem_primeFactors hp) hs)
    _ ≤ Real.log N := sum_log_primeFactors_le_log N

end BombieriVinogradov.SiegelWalfisz
