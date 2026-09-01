import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelDerivative
import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumBound

/-!
# Uniform majorant for the character Abel-kernel derivative

This module owns the pointwise norm estimate on a complex ball around a
parameter with positive real part.
-/

set_option autoImplicit false

open Finset Set

namespace BombieriVinogradov

/-- On the standard half-real-part ball, the Abel-kernel derivative has a fixed majorant. -/
theorem norm_characterAbelKernelDerivative_le {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1)
    {s0 z : Complex} (hz : z ∈ Metric.ball s0 (s0.re / 2))
    {t : Real} (ht : 1 < t) :
    ‖-((Real.log t : Real) : Complex) *
        ((∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(z + 1)))‖ ≤
      (N : Real) * (Real.log t * t ^ (-(s0.re / 2 + 1))) := by
  have hDist : ‖z - s0‖ < s0.re / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hReAbs : |z.re - s0.re| ≤ ‖z - s0‖ := by
    simpa using Complex.abs_re_le_norm (z - s0)
  have hReLower : s0.re / 2 < z.re := by
    have hAbsLt : |z.re - s0.re| < s0.re / 2 := lt_of_le_of_lt hReAbs hDist
    linarith [(abs_lt.mp hAbsLt).1]
  have htPos : 0 < t := zero_lt_one.trans ht
  have htOne : 1 ≤ t := ht.le
  have hLogNonneg : 0 ≤ Real.log t := Real.log_nonneg htOne
  have hPower : ‖(t : Complex) ^ (-(z + 1))‖ ≤
      t ^ (-(s0.re / 2 + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    apply Real.rpow_le_rpow_of_exponent_le htOne
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hLogNonneg, norm_mul]
  calc
    Real.log t *
          (‖∑ k ∈ Icc 1 ⌊t⌋₊, chi k‖ * ‖(t : Complex) ^ (-(z + 1))‖) ≤
        Real.log t * ((N : Real) * t ^ (-(s0.re / 2 + 1))) := by
      gcongr
      exact norm_sum_character_Icc_le_modulus chi hchi ⌊t⌋₊
    _ = (N : Real) * (Real.log t * t ^ (-(s0.re / 2 + 1))) := by ring

end BombieriVinogradov
