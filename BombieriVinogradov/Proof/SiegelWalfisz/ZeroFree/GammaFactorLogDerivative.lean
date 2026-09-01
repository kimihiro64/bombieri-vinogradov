import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaRealLogDerivative

/-!
# Logarithmic derivative of a Dirichlet gamma factor

This module specializes the `Gammaℝ` logarithmic derivative to the even and odd
Dirichlet-character gamma factors.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_gammaFactor_of_even
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hEven : DirichletCharacter.Even chi) {s : Complex} (hs : 0 < s.re) :
    logDeriv chi.gammaFactor s =
      -(Real.log Real.pi : Complex) / 2 +
        (1 / 2 : Complex) * Complex.digamma (s / 2) := by
  have hFunction : chi.gammaFactor = Complex.Gammaℝ := by
    funext z
    exact hEven.gammaFactor_def z
  rw [hFunction]
  exact logDeriv_Gammaℝ_eq_digamma hs

theorem logDeriv_gammaFactor_of_odd
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hOdd : DirichletCharacter.Odd chi) {s : Complex} (hs : 0 < s.re) :
    logDeriv chi.gammaFactor s =
      -(Real.log Real.pi : Complex) / 2 +
        (1 / 2 : Complex) * Complex.digamma ((s + 1) / 2) := by
  have hShiftPositive : 0 < (s + 1).re := by
    simp
    linarith
  have hFunction : chi.gammaFactor =
      Complex.Gammaℝ ∘ fun z : Complex => z + 1 := by
    funext z
    exact hOdd.gammaFactor_def z
  rw [hFunction]
  have hComp :=
    logDeriv_comp
      (f := Complex.Gammaℝ) (g := fun z : Complex => z + 1) (x := s)
      (Complex.differentiableAt_Gammaℝ_of_re_pos hShiftPositive)
      ((differentiable_id.add_const (1 : Complex)).differentiableAt)
  rw [hComp, logDeriv_Gammaℝ_eq_digamma hShiftPositive]
  simp

end BombieriVinogradov.SiegelWalfisz
