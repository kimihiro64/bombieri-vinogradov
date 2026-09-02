import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorNearOrigin

/-!
# Differentiability of Dirichlet gamma factors near the origin

This module proves regularity of the parity-selected Dirichlet gamma factor in
the open strip to the right of real part minus one, away from the even factor's
excluded origin.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The parity-selected Dirichlet gamma factor is differentiable at every
nonzero point whose real part is strictly greater than minus one. -/
theorem DirichletCharacter.differentiableAt_gammaFactor_of_neg_one_lt_re_of_ne_zero
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : -1 < s.re) (hs0 : Ne s 0) :
    DifferentiableAt Complex chi.gammaFactor s := by
  cases chi.even_or_odd with
  | inl hEven =>
    unfold DirichletCharacter.gammaFactor
    simp only [if_pos hEven]
    refine DifferentiableAt.mul ?_ ?_
    exact ((differentiable_id.neg.div_const 2).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt
    apply (Complex.differentiableAt_Gamma (s / 2) ?_).comp s
      ((differentiable_id.div_const (2 : Complex)).differentiableAt)
    intro m hPole
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
  | inr hOdd =>
    unfold DirichletCharacter.gammaFactor
    simp only [if_neg hOdd.not_even]
    refine DifferentiableAt.mul ?_ ?_
    exact (((differentiable_id.add_const (1 : Complex)).neg.div_const 2).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt
    apply (Complex.differentiableAt_Gamma ((s + 1) / 2) ?_).comp s
      (((differentiable_id.add_const (1 : Complex)).div_const
        (2 : Complex)).differentiableAt)
    intro m hPole
    have hPositive : 0 < ((s + 1) / 2).re := by
      rw [Complex.div_ofNat_re]
      simp only [Complex.add_re, Complex.one_re]
      linarith
    rw [hPole] at hPositive
    have hNonpositive : (-(m : Complex)).re <= 0 := by norm_num
    exact (not_lt_of_ge hNonpositive) hPositive

end BombieriVinogradov.SiegelWalfisz
