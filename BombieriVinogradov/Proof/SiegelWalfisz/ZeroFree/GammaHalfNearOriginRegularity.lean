import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorNearOrigin

/-!
# Regularity of the half-argument Gamma function near the origin

This module isolates pole exclusion, nonvanishing, and differentiability for
the half-argument Gamma function in the strip needed by the left contour.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero
    {s : Complex} (hs : -1 < s.re) (hs0 : Ne s 0) (m : Nat) :
    Ne (s / 2) (-(m : Complex)) := by
  intro hPole
  have hEq : s = -(2 * (m : Complex)) := by
    calc
      s = (s / 2) * 2 := by ring
      _ = (-(m : Complex)) * 2 := by rw [hPole]
      _ = -(2 * (m : Complex)) := by ring
  cases m with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, neg_zero] at hEq
    exact hs0 hEq
  | succ m =>
    have hRe : s.re <= -2 := by
      rw [hEq]
      norm_num [Complex.mul_re]
    linarith

theorem Gamma_half_ne_zero_of_neg_one_lt_re_of_ne_zero
    {s : Complex} (hs : -1 < s.re) (hs0 : Ne s 0) :
    Ne (Complex.Gamma (s / 2)) 0 := by
  apply Complex.Gamma_ne_zero
  exact half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero hs hs0

theorem differentiableAt_Gamma_half_of_neg_one_lt_re_of_ne_zero
    {s : Complex} (hs : -1 < s.re) (hs0 : Ne s 0) :
    DifferentiableAt Complex (fun z : Complex => Complex.Gamma (z / 2)) s := by
  apply (Complex.differentiableAt_Gamma (s / 2) ?_).comp s
    ((differentiable_id.div_const (2 : Complex)).differentiableAt)
  exact half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero hs hs0

end BombieriVinogradov.SiegelWalfisz
