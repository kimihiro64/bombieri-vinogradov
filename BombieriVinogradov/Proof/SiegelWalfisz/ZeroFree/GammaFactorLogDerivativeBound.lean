import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorEvenLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorOddLogDerivativeBound

/-!
# Uniform gamma-factor logarithmic-derivative bound

This module combines the even and odd estimates into one absolute constant independent
of the modulus, character, and point in the strip `1 < re s ≤ 2`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_gammaFactor_le_log :
    exists C : Real, 0 < C ∧
      forall {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex},
        1 < s.re -> s.re ≤ 2 ->
          ‖logDeriv chi.gammaFactor s‖ ≤
            C * Real.log (|s.im| + 2) := by
  obtain ⟨Ceven, hCevenPos, hCeven⟩ :=
    exists_norm_logDeriv_gammaFactor_le_log_of_even
  obtain ⟨Codd, hCoddPos, hCodd⟩ :=
    exists_norm_logDeriv_gammaFactor_le_log_of_odd
  refine Exists.intro (Ceven + Codd) (And.intro (add_pos hCevenPos hCoddPos) ?_)
  intro N chi s hsLower hsUpper
  have hLogNonneg : 0 ≤ Real.log (|s.im| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg s.im]
  rcases chi.even_or_odd with hEven | hOdd
  · calc
      ‖logDeriv chi.gammaFactor s‖ ≤
          Ceven * Real.log (|s.im| + 2) :=
        hCeven hEven hsLower hsUpper
      _ ≤ (Ceven + Codd) * Real.log (|s.im| + 2) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hCoddPos.le) hLogNonneg
  · calc
      ‖logDeriv chi.gammaFactor s‖ ≤
          Codd * Real.log (|s.im| + 2) :=
        hCodd hOdd hsLower hsUpper
      _ ≤ (Ceven + Codd) * Real.log (|s.im| + 2) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hCevenPos.le) hLogNonneg

end BombieriVinogradov.SiegelWalfisz
