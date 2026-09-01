import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumBound
import BombieriVinogradov.Helpers.DirichletCharacter.RpowTailIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Norm bound for the character Abel-kernel integral

This module owns the integral estimate before multiplication by the outer
complex parameter.
-/

set_option autoImplicit false

open Filter Finset MeasureTheory Set

namespace BombieriVinogradov

/-- The Abel-kernel integral has norm at most `N / re(s)` for positive real part. -/
theorem norm_characterAbelKernelIntegral_le {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1)
    {s : Complex} (hs : 0 < s.re) :
    ‖∫ t in Ioi (1 : Real),
        (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1))‖ ≤
      (N : Real) / s.re := by
  have hRpowIntegrable : IntegrableOn
      (fun t : Real => t ^ (-(s.re + 1))) (Ioi 1) := by
    exact (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)
  have hMajorantIntegrable : IntegrableOn
      (fun t : Real => (N : Real) * t ^ (-(s.re + 1))) (Ioi 1) :=
    hRpowIntegrable.const_mul (N : Real)
  have hNormBound : ∀ᵐ t : Real ∂volume.restrict (Ioi (1 : Real)),
      ‖(∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1))‖ ≤
        (N : Real) * t ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := zero_lt_one.trans ht
    have hPowerNonneg : 0 ≤ t ^ (-(s.re + 1)) := Real.rpow_nonneg htPos.le _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right
      (norm_sum_character_Icc_le_modulus chi hchi ⌊t⌋₊) hPowerNonneg
  calc
    ‖∫ t in Ioi (1 : Real),
        (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1))‖ ≤
        ∫ t in Ioi (1 : Real), (N : Real) * t ^ (-(s.re + 1)) :=
      norm_integral_le_of_norm_le hMajorantIntegrable hNormBound
    _ = (N : Real) * (1 / s.re) := by
      rw [integral_const_mul, integral_Ioi_rpow_neg_add_one hs]
    _ = (N : Real) / s.re := by ring

end BombieriVinogradov
