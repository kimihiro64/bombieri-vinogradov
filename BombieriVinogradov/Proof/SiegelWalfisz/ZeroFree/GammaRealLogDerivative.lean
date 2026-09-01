import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorRegularity
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Logarithmic derivative of Deligne's real gamma factor

This module computes the logarithmic derivative of `Complex.Gammaℝ` in the positive
half-plane as the sum of its power normalization and digamma contributions.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_Gammaℝ_eq_digamma
    {s : Complex} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -(Real.log Real.pi : Complex) / 2 +
        (1 / 2 : Complex) * Complex.digamma (s / 2) := by
  let power : Complex -> Complex := fun z => (Real.pi : Complex) ^ (-z / 2)
  let gamma : Complex -> Complex := fun z => Complex.Gamma (z / 2)
  have hPowerNe : power s ≠ 0 := by
    simp [power, Real.pi_ne_zero]
  have hPowerDifferentiable : DifferentiableAt Complex power s := by
    exact ((differentiable_id.neg.div_const 2).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt
  have hHalfRe : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    exact div_pos hs (by norm_num)
  have hGammaNe : gamma s ≠ 0 := by
    exact Complex.Gamma_ne_zero_of_re_pos hHalfRe
  have hGammaBaseDifferentiable :
      DifferentiableAt Complex Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma (s / 2)
    intro m hPole
    have hNonpositive : (s / 2).re ≤ 0 := by
      rw [hPole]
      simp
    linarith
  have hGammaDifferentiable : DifferentiableAt Complex gamma s :=
    hGammaBaseDifferentiable.comp s
      ((differentiable_id.div_const (2 : Complex)).differentiableAt)
  have hProduct : Complex.Gammaℝ = fun z => power z * gamma z := by
    funext z
    exact Complex.Gammaℝ_def z
  have hSplit :
      logDeriv Complex.Gammaℝ s = logDeriv power s + logDeriv gamma s := by
    rw [hProduct]
    exact logDeriv_mul s hPowerNe hGammaNe
      hPowerDifferentiable hGammaDifferentiable
  have hPower :
      logDeriv power s = -(Real.log Real.pi : Complex) / 2 := by
    rw [logDeriv_apply,
      Complex.deriv_const_cpow
        (f := fun z : Complex => -z / 2) (by fun_prop)]
    simp [power, Real.pi_ne_zero, Complex.ofReal_log Real.pi_pos.le]
    ring
  have hGamma :
      logDeriv gamma s = (1 / 2 : Complex) * Complex.digamma (s / 2) := by
    have hComp :=
      logDeriv_comp
        (f := Complex.Gamma) (g := fun z : Complex => z / 2) (x := s)
        hGammaBaseDifferentiable
        ((differentiable_id.div_const (2 : Complex)).differentiableAt)
    change logDeriv (Complex.Gamma ∘ fun z : Complex => z / 2) s = _
    rw [hComp, ← Complex.digamma_def]
    simp
    ring
  rw [hSplit, hPower, hGamma]

end BombieriVinogradov.SiegelWalfisz
