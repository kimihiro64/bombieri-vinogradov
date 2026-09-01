import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerFactor
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerProduct
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimeDivisorLogSum

/-!
# Logarithmic-derivative cost of changing character level

This is Strombergsson equation (404): replacing a nonprincipal character by
its primitive inducing character costs at most the logarithm of the ambient
modulus throughout the closed half-plane `1 <= re s`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_logDeriv_LFunction_sub_primitive_le_log
    {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : Complex} (hs : 1 ≤ s.re) :
    ‖logDeriv chi.LFunction s -
      logDeriv chi.primitiveCharacter.LFunction s‖ ≤ Real.log N := by
  have hSplit :=
    logDeriv_LFunction_eq_primitive_add_levelCorrection chi hchi hs
  have hDifference :
      logDeriv chi.LFunction s -
          logDeriv chi.primitiveCharacter.LFunction s =
        logDeriv (levelCorrection chi) s := by
    rw [hSplit]
    abel
  rw [hDifference, logDeriv_levelCorrection_eq_sum chi hchi hs]
  calc
    ‖∑ p ∈ N.primeFactors,
        logDeriv (levelCorrectionFactor chi p) s‖ ≤
        ∑ p ∈ N.primeFactors,
          ‖logDeriv (levelCorrectionFactor chi p) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ N.primeFactors, Real.log p :=
      Finset.sum_le_sum (fun p hp =>
        norm_logDeriv_levelCorrectionFactor_le_log chi
          (Nat.prime_of_mem_primeFactors hp) hs)
    _ ≤ Real.log N := sum_log_primeFactors_le_log N

end BombieriVinogradov.SiegelWalfisz
