import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionDefinitions
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# A differentiated level-correction Euler factor

This module computes one local logarithmic derivative and proves its
`Real.log p` majorant on the closed half-plane `1 <= re s`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_levelCorrectionFactor {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (p : Nat) (s : Complex) :
    logDeriv (levelCorrectionFactor chi p) s =
      chi.primitiveCharacter p * (Real.log p : Complex) *
        (p : Complex) ^ (-s) / levelCorrectionFactor chi p s := by
  rw [logDeriv_apply]
  change deriv
      (fun z : Complex =>
        1 - chi.primitiveCharacter p * (p : Complex) ^ (-z)) s /
      (1 - chi.primitiveCharacter p * (p : Complex) ^ (-s)) = _
  rw [deriv_const_sub, deriv_const_mul_field,
    Complex.deriv_const_cpow (f := fun z : Complex => -z) (by fun_prop)]
  simp [Complex.natCast_log]
  rw [levelCorrectionFactor]
  ring

theorem differentiableAt_levelCorrectionFactor {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) {p : Nat} (hp : p.Prime)
    (s : Complex) :
    DifferentiableAt Complex (levelCorrectionFactor chi p) s := by
  change DifferentiableAt Complex
    (fun z : Complex =>
      1 - chi.primitiveCharacter p * (p : Complex) ^ (-z)) s
  apply DifferentiableAt.sub
  · fun_prop
  · apply DifferentiableAt.mul
    · fun_prop
    · exact ((hasDerivAt_neg s).const_cpow
        (.inl (Nat.cast_ne_zero.mpr hp.ne_zero))).differentiableAt

theorem norm_prime_cpow_le_one_half_of_one_le {p : Nat} (hp : p.Prime)
    {s : Complex} (hs : 1 ≤ s.re) :
    ‖(p : Complex) ^ (-s)‖ ≤ 1 / 2 := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by
    rw [Complex.neg_re]
    linarith)]
  refine (Real.rpow_le_rpow_of_nonpos zero_lt_two
    (Nat.cast_le.mpr hp.two_le) (by
      rw [Complex.neg_re]
      linarith)).trans ?_
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by
    rw [Complex.neg_re]
    linarith)

theorem one_half_le_norm_levelCorrectionFactor {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) {p : Nat} (hp : p.Prime)
    {s : Complex} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖levelCorrectionFactor chi p s‖ := by
  have hPower := norm_prime_cpow_le_one_half_of_one_le hp hs
  have hCharacter : ‖chi.primitiveCharacter p‖ ≤ 1 :=
    _root_.DirichletCharacter.norm_le_one chi.primitiveCharacter p
  have hProduct :
      ‖chi.primitiveCharacter p * (p : Complex) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc
      ‖chi.primitiveCharacter p‖ * ‖(p : Complex) ^ (-s)‖ ≤
          1 * (1 / 2) :=
        mul_le_mul hCharacter hPower (norm_nonneg _) zero_le_one
      _ = 1 / 2 := by ring
  have hReverse :
      1 - ‖chi.primitiveCharacter p * (p : Complex) ^ (-s)‖ ≤
        ‖1 - chi.primitiveCharacter p * (p : Complex) ^ (-s)‖ := by
    simpa only [norm_one] using
      norm_sub_norm_le (1 : Complex)
        (chi.primitiveCharacter p * (p : Complex) ^ (-s))
  rw [levelCorrectionFactor]
  linarith

theorem norm_logDeriv_levelCorrectionFactor_le_log {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) {p : Nat} (hp : p.Prime)
    {s : Complex} (hs : 1 ≤ s.re) :
    ‖logDeriv (levelCorrectionFactor chi p) s‖ ≤ Real.log p := by
  have hPower := norm_prime_cpow_le_one_half_of_one_le hp hs
  have hCharacter : ‖chi.primitiveCharacter p‖ ≤ 1 :=
    _root_.DirichletCharacter.norm_le_one chi.primitiveCharacter p
  have hLog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hCharacterLog :
      ‖chi.primitiveCharacter p‖ * Real.log p ≤ Real.log p := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hCharacter hLog
  have hNumerator :
      ‖chi.primitiveCharacter p * (Real.log p : Complex) *
        (p : Complex) ^ (-s)‖ ≤ Real.log p / 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hLog]
    calc
      ‖chi.primitiveCharacter p‖ * Real.log p *
          ‖(p : Complex) ^ (-s)‖ ≤
          Real.log p * (1 / 2) :=
        mul_le_mul hCharacterLog hPower (norm_nonneg _) hLog
      _ = Real.log p / 2 := by ring
  have hDenominator := one_half_le_norm_levelCorrectionFactor chi hp hs
  have hDenominatorPos : 0 < ‖levelCorrectionFactor chi p s‖ :=
    (show (0 : Real) < 1 / 2 by norm_num).trans_le hDenominator
  rw [logDeriv_levelCorrectionFactor chi p s, norm_div]
  calc
    ‖chi.primitiveCharacter p * (Real.log p : Complex) *
        (p : Complex) ^ (-s)‖ / ‖levelCorrectionFactor chi p s‖ ≤
        (Real.log p / 2) / ‖levelCorrectionFactor chi p s‖ :=
      div_le_div_of_nonneg_right hNumerator (norm_nonneg _)
    _ ≤ (Real.log p / 2) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hDenominator
    _ = Real.log p := by ring

end BombieriVinogradov.SiegelWalfisz
