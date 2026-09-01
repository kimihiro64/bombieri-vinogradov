import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Regularity of Dirichlet gamma factors

This module proves nonvanishing and differentiability of the parity-selected Dirichlet
gamma factor in the positive half-plane.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem Complex.differentiableAt_Gammaℝ_of_re_pos
    {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex Complex.Gammaℝ s := by
  unfold Complex.Gammaℝ
  apply DifferentiableAt.mul
  · exact ((differentiable_id.neg.div_const 2).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt
  · apply (Complex.differentiableAt_Gamma (s / 2) ?_).comp s
      ((differentiable_id.div_const (2 : Complex)).differentiableAt)
    intro m hPole
    have hPositive : 0 < (s / 2).re := by
      rw [Complex.div_ofNat_re]
      exact div_pos hs (by norm_num)
    have hNonpositive : (s / 2).re ≤ 0 := by
      rw [hPole]
      simp
    linarith

theorem DirichletCharacter.gammaFactor_ne_zero_of_re_pos
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 0 < s.re) : chi.gammaFactor s ≠ 0 := by
  rcases chi.even_or_odd with hEven | hOdd
  · rw [hEven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hOdd.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp
    linarith

theorem DirichletCharacter.gammaFactor_ne_zero_of_one_lt_re
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) : chi.gammaFactor s ≠ 0 :=
  DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (lt_trans zero_lt_one hs)

theorem DirichletCharacter.differentiableAt_gammaFactor_of_re_pos
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 0 < s.re) : DifferentiableAt Complex chi.gammaFactor s := by
  rcases chi.even_or_odd with hEven | hOdd
  · have hFunction : chi.gammaFactor = Complex.Gammaℝ := by
      funext z
      exact hEven.gammaFactor_def z
    rw [hFunction]
    exact Complex.differentiableAt_Gammaℝ_of_re_pos hs
  · have hFunction : chi.gammaFactor = fun z => Complex.Gammaℝ (z + 1) := by
      funext z
      exact hOdd.gammaFactor_def z
    rw [hFunction]
    apply (Complex.differentiableAt_Gammaℝ_of_re_pos (s := s + 1) ?_).comp s
      ((differentiable_id.add_const (1 : Complex)).differentiableAt)
    simp
    linarith

theorem DirichletCharacter.differentiableAt_gammaFactor_of_one_lt_re
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) : DifferentiableAt Complex chi.gammaFactor s :=
  DirichletCharacter.differentiableAt_gammaFactor_of_re_pos
    chi (lt_trans zero_lt_one hs)

end BombieriVinogradov.SiegelWalfisz
