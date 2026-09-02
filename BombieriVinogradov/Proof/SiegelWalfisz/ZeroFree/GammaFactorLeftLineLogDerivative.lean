import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaHalfNearOriginRegularity
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Logarithmic derivatives of Dirichlet gamma factors near the left line

This module derives exact parity-specific formulas. Analytic norm estimates
belong to separate downstream modules.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_pi_cpow_mul_Gamma_half_add
    {shift s : Complex}
    (hGammaNe : Ne (Complex.Gamma ((s + shift) / 2)) 0)
    (hGammaDifferentiable :
      DifferentiableAt Complex Complex.Gamma ((s + shift) / 2)) :
    logDeriv
        (fun z : Complex =>
          (Real.pi : Complex) ^ (-(z + shift) / 2) *
            Complex.Gamma ((z + shift) / 2)) s =
      -(Real.log Real.pi : Complex) / 2 +
        (1 / 2 : Complex) * Complex.digamma ((s + shift) / 2) := by
  let power : Complex -> Complex :=
    fun z => (Real.pi : Complex) ^ (-(z + shift) / 2)
  let gamma : Complex -> Complex :=
    fun z => Complex.Gamma ((z + shift) / 2)
  have hPowerNe : Ne (power s) 0 := by
    simp [power, Real.pi_ne_zero]
  have hPowerDifferentiable : DifferentiableAt Complex power s := by
    exact (((differentiable_id.add_const shift).neg.div_const 2).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt
  have hGammaDifferentiableAt : DifferentiableAt Complex gamma s :=
    hGammaDifferentiable.comp s
      (((differentiable_id.add_const shift).div_const
        (2 : Complex)).differentiableAt)
  have hSplit :
      logDeriv (fun z : Complex => power z * gamma z) s =
        logDeriv power s + logDeriv gamma s :=
    logDeriv_mul s hPowerNe hGammaNe
      hPowerDifferentiable hGammaDifferentiableAt
  have hPower :
      logDeriv power s = -(Real.log Real.pi : Complex) / 2 := by
    rw [logDeriv_apply,
      Complex.deriv_const_cpow
        (f := fun z : Complex => -(z + shift) / 2) (by fun_prop)]
    simp [power, Real.pi_ne_zero, Complex.ofReal_log Real.pi_pos.le]
    ring
  have hGamma :
      logDeriv gamma s =
        (1 / 2 : Complex) * Complex.digamma ((s + shift) / 2) := by
    have hComp :=
      logDeriv_comp
        (f := Complex.Gamma)
        (g := fun z : Complex => (z + shift) / 2)
        (x := s)
        hGammaDifferentiable
        (((differentiable_id.add_const shift).div_const
          (2 : Complex)).differentiableAt)
    change logDeriv
      (Function.comp Complex.Gamma (fun z : Complex => (z + shift) / 2)) s = _
    rw [hComp, Complex.digamma_def]
    simp
    ring
  change logDeriv (fun z : Complex => power z * gamma z) s = _
  rw [hSplit, hPower, hGamma]

theorem logDeriv_gammaFactor_of_even_of_neg_one_lt_re_of_ne_zero
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hEven : DirichletCharacter.Even chi) {s : Complex}
    (hs : -1 < s.re) (hs0 : Ne s 0) :
    logDeriv chi.gammaFactor s =
      -(Real.log Real.pi : Complex) / 2 +
        (1 / 2 : Complex) * Complex.digamma (s / 2) := by
  unfold DirichletCharacter.gammaFactor
  simp only [if_pos hEven]
  change logDeriv
    (fun z : Complex =>
      (Real.pi : Complex) ^ (-z / 2) * Complex.Gamma (z / 2)) s = _
  have hGammaNe :=
    Gamma_half_ne_zero_of_neg_one_lt_re_of_ne_zero hs hs0
  have hGammaDifferentiable :
      DifferentiableAt Complex Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2)
      (half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero hs hs0)
  have hIdentity :=
    logDeriv_pi_cpow_mul_Gamma_half_add
      (shift := 0) (s := s)
      (by simpa only [add_zero] using hGammaNe)
      (by simpa only [add_zero] using hGammaDifferentiable)
  simpa only [add_zero] using hIdentity

theorem logDeriv_gammaFactor_of_odd_of_neg_one_lt_re
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hOdd : DirichletCharacter.Odd chi) {s : Complex}
    (hs : -1 < s.re) :
    logDeriv chi.gammaFactor s =
      -(Real.log Real.pi : Complex) / 2 +
        (1 / 2 : Complex) * Complex.digamma ((s + 1) / 2) := by
  have hArgumentPositive : 0 < ((s + 1) / 2).re := by
    rw [Complex.div_ofNat_re]
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hGammaNe : Ne (Complex.Gamma ((s + 1) / 2)) 0 :=
    Complex.Gamma_ne_zero_of_re_pos hArgumentPositive
  have hGammaDifferentiable :
      DifferentiableAt Complex Complex.Gamma ((s + 1) / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hPole
    have hNonpositive : (-(m : Complex)).re <= 0 := by norm_num
    rw [hPole] at hArgumentPositive
    exact (not_lt_of_ge hNonpositive) hArgumentPositive
  unfold DirichletCharacter.gammaFactor
  simp only [if_neg hOdd.not_even]
  change logDeriv
    (fun z : Complex =>
      (Real.pi : Complex) ^ (-(z + 1) / 2) *
        Complex.Gamma ((z + 1) / 2)) s = _
  exact logDeriv_pi_cpow_mul_Gamma_half_add
    (shift := 1) (s := s) hGammaNe hGammaDifferentiable

end BombieriVinogradov.SiegelWalfisz
