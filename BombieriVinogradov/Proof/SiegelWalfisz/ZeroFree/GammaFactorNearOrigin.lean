import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorRegularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Dirichlet gamma factors near the origin

This module isolates the parity calculation showing that the Dirichlet gamma
factor has no zeros in the open strip to the right of real part minus one,
apart from the even factor's excluded origin.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The parity-selected Dirichlet gamma factor is nonzero at every nonzero
point whose real part is strictly greater than minus one. -/
theorem DirichletCharacter.gammaFactor_ne_zero_of_neg_one_lt_re_of_ne_zero
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : -1 < s.re) (hs0 : Ne s 0) :
    Ne (chi.gammaFactor s) 0 := by
  cases chi.even_or_odd with
  | inl hEven =>
    rw [DirichletCharacter.gammaFactor, if_pos hEven]
    change Ne
      ((Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2)) 0
    have hPower : Ne ((Real.pi : Complex) ^ (-s / 2)) 0 :=
      Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hGamma : Ne (Complex.Gamma (s / 2)) 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have hEq : s = -(2 * (n : Complex)) := by
        calc
          s = (s / 2) * 2 := by ring
          _ = (-(n : Complex)) * 2 := by rw [hn]
          _ = -(2 * (n : Complex)) := by ring
      cases n with
      | zero =>
        simp only [Nat.cast_zero, mul_zero, neg_zero] at hEq
        exact hs0 hEq
      | succ n =>
        have hRe : s.re <= -2 := by
          rw [hEq]
          norm_num [Complex.mul_re]
        linarith
    exact mul_ne_zero hPower hGamma
  | inr hOdd =>
    rw [DirichletCharacter.gammaFactor, if_neg hOdd.not_even]
    change Ne
      ((Real.pi : Complex) ^ (-(s + 1) / 2) *
        Complex.Gamma ((s + 1) / 2)) 0
    have hPower : Ne ((Real.pi : Complex) ^ (-(s + 1) / 2)) 0 :=
      Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hGamma : Ne (Complex.Gamma ((s + 1) / 2)) 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have hPositive : 0 < ((s + 1) / 2).re := by
        rw [Complex.div_ofNat_re]
        simp only [Complex.add_re, Complex.one_re]
        linarith
      rw [hn] at hPositive
      have hNonpositive : (-(n : Complex)).re <= 0 := by norm_num
      exact (not_lt_of_ge hNonpositive) hPositive
    exact mul_ne_zero hPower hGamma

end BombieriVinogradov.SiegelWalfisz
