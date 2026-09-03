import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorEvenHorizontalLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorOddHorizontalLogDerivativeBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Character-uniform gamma bound on the horizontal contour strip

This thin module combines the separately proved even and odd estimates.
Zero sums and contour integration remain outside this parity boundary.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_gammaFactor_horizontal_strip_le_log :
    exists C : Real, And (0 < C)
      (forall {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex},
        -(1 : Real) / 2 <= s.re ->
        s.re <= 2 ->
        2 <= abs s.im ->
          norm (logDeriv chi.gammaFactor s) <=
            C * Real.log (abs s.im + 2)) := by
  choose Ceven hCevenPos hCeven using
    exists_norm_logDeriv_gammaFactor_le_log_of_even_horizontal_strip
  choose Codd hCoddPos hCodd using
    exists_norm_logDeriv_gammaFactor_le_log_of_odd_horizontal_strip
  refine Exists.intro (Ceven + Codd)
    (And.intro (add_pos hCevenPos hCoddPos) ?_)
  intro N chi s hsLower hsUpper hsIm
  have hLogNonneg : 0 <= Real.log (abs s.im + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg s.im]
  cases chi.even_or_odd with
  | inl hEven =>
    calc
      norm (logDeriv chi.gammaFactor s) <=
          Ceven * Real.log (abs s.im + 2) :=
        hCeven hEven hsLower hsUpper hsIm
      _ <= (Ceven + Codd) * Real.log (abs s.im + 2) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hCoddPos.le) hLogNonneg
  | inr hOdd =>
    calc
      norm (logDeriv chi.gammaFactor s) <=
          Codd * Real.log (abs s.im + 2) :=
        hCodd hOdd hsLower hsUpper hsIm
      _ <= (Ceven + Codd) * Real.log (abs s.im + 2) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hCevenPos.le) hLogNonneg

end BombieriVinogradov.SiegelWalfisz

