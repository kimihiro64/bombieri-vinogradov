import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerFactor
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalLevelCorrectionDefinitions

/-!
# One principal-character correction factor

This module differentiates `1 - p^(-s)` and proves the local `log p` bound
used by the finite principal-character correction product.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_principalLevelCorrectionFactor
    (p : Nat) (s : Complex) :
    logDeriv (principalLevelCorrectionFactor p) s =
      (Real.log p : Complex) * (p : Complex) ^ (-s) /
        principalLevelCorrectionFactor p s := by
  rw [logDeriv_apply]
  change deriv (fun z : Complex => 1 - (p : Complex) ^ (-z)) s /
      (1 - (p : Complex) ^ (-s)) = _
  rw [deriv_const_sub,
    Complex.deriv_const_cpow (f := fun z : Complex => -z) (by fun_prop)]
  simp [Complex.natCast_log]
  rw [principalLevelCorrectionFactor]

theorem differentiableAt_principalLevelCorrectionFactor
    {p : Nat} (hp : p.Prime) (s : Complex) :
    DifferentiableAt Complex (principalLevelCorrectionFactor p) s := by
  change DifferentiableAt Complex
    (fun z : Complex => 1 - (p : Complex) ^ (-z)) s
  apply DifferentiableAt.sub
  · fun_prop
  · exact ((hasDerivAt_neg s).const_cpow
      (.inl (Nat.cast_ne_zero.mpr hp.ne_zero))).differentiableAt

theorem one_half_le_norm_principalLevelCorrectionFactor
    {p : Nat} (hp : p.Prime) {s : Complex} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖principalLevelCorrectionFactor p s‖ := by
  have hPower := norm_prime_cpow_le_one_half_of_one_le hp hs
  have hReverse :
      1 - ‖(p : Complex) ^ (-s)‖ ≤
        ‖1 - (p : Complex) ^ (-s)‖ := by
    simpa only [norm_one] using
      norm_sub_norm_le (1 : Complex) ((p : Complex) ^ (-s))
  rw [principalLevelCorrectionFactor]
  linarith

theorem norm_logDeriv_principalLevelCorrectionFactor_le_log
    {p : Nat} (hp : p.Prime) {s : Complex} (hs : 1 ≤ s.re) :
    ‖logDeriv (principalLevelCorrectionFactor p) s‖ ≤ Real.log p := by
  have hPower := norm_prime_cpow_le_one_half_of_one_le hp hs
  have hLog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hNumerator :
      ‖(Real.log p : Complex) * (p : Complex) ^ (-s)‖ ≤
        Real.log p / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hLog]
    exact (mul_le_mul_of_nonneg_left hPower hLog).trans_eq (by ring)
  have hDenominator :=
    one_half_le_norm_principalLevelCorrectionFactor hp hs
  have hDenominatorPos :
      0 < ‖principalLevelCorrectionFactor p s‖ :=
    (show (0 : Real) < 1 / 2 by norm_num).trans_le hDenominator
  rw [logDeriv_principalLevelCorrectionFactor p s, norm_div]
  calc
    ‖(Real.log p : Complex) * (p : Complex) ^ (-s)‖ /
          ‖principalLevelCorrectionFactor p s‖ ≤
        (Real.log p / 2) / ‖principalLevelCorrectionFactor p s‖ :=
      div_le_div_of_nonneg_right hNumerator (norm_nonneg _)
    _ ≤ (Real.log p / 2) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hDenominator
    _ = Real.log p := by ring

end BombieriVinogradov.SiegelWalfisz
