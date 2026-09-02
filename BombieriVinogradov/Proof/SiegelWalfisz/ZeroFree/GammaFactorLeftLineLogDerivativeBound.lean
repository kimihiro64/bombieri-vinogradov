import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorEvenLeftLineLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorOddLeftLineLogDerivativeBound

/-!
# Uniform gamma-factor bound on the explicit-formula left line

This module combines the independently proved even and odd estimates into one
absolute character-uniform constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_gammaFactor_left_line_le_log :
    exists C : Real, And (0 < C)
      (forall {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex},
        s.re = -(1 : Real) / 2 ->
          norm (logDeriv chi.gammaFactor s) <=
            C * Real.log (abs s.im + 2)) := by
  choose Ceven hCevenPos hCeven using
    exists_norm_logDeriv_gammaFactor_left_line_le_log_of_even
  choose Codd hCoddPos hCodd using
    exists_norm_logDeriv_gammaFactor_left_line_le_log_of_odd
  refine Exists.intro (Ceven + Codd)
    (And.intro (add_pos hCevenPos hCoddPos) ?_)
  intro N chi s hsRe
  have hLogNonneg : 0 <= Real.log (abs s.im + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg s.im]
  cases chi.even_or_odd with
  | inl hEven =>
    calc
      norm (logDeriv chi.gammaFactor s) <=
          Ceven * Real.log (abs s.im + 2) :=
        hCeven hEven hsRe
      _ <= (Ceven + Codd) * Real.log (abs s.im + 2) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hCoddPos.le) hLogNonneg
  | inr hOdd =>
    calc
      norm (logDeriv chi.gammaFactor s) <=
          Codd * Real.log (abs s.im + 2) :=
        hCodd hOdd hsRe
      _ <= (Ceven + Codd) * Real.log (abs s.im + 2) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hCevenPos.le) hLogNonneg

end BombieriVinogradov.SiegelWalfisz
