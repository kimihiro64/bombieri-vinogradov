import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.Core
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.OuterRangeAlgebra
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.OuterRangeMass
import Mathlib.Tactic

/-!
# Final estimate for the outer Vaughan range

When `X <= Q^2`, the maximal von Mangoldt character sum is treated directly as
a one-by-`X` maximal bilinear sum. This module only composes the exact encoding,
coefficient-mass bounds, and real algebra proved in the three inward modules.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

theorem vaughanMean_le_outerRange
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) (hXQ : X <= Q ^ 2) :
    vaughanMean X Q <=
      6480 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  have hraw := weightedMaximalBilinear_le_cutoffFactor X 1 X Q
    outerRangeUnitCoefficient outerRangeMangoldtCoefficient hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  simp_rw [maximalBilinearNorm_outerRange_eq] at hraw
  change vaughanMean X Q <= _ at hraw
  simp only [Nat.cast_one, outerRangeUnitCoefficient_mass, mul_one] at hraw
  have hcutoff : 0 <= 16 + 4 * Real.log ((X : Real) + 1) := by
    have hlog : 0 <= Real.log ((X : Real) + 1) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= X + 1 by omega)
    positivity
  have hmassSecond :
      Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
          coefficientMass outerRangeMangoldtCoefficient X) <=
        Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
          ((X : Real) * Real.log (X : Real) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left
      (outerRangeMangoldtCoefficient_mass_le X) (by positivity)
  have hmassProduct :
      Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            coefficientMass outerRangeMangoldtCoefficient X) <=
        Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            ((X : Real) * Real.log (X : Real) ^ 2)) :=
    mul_le_mul_of_nonneg_left hmassSecond (Real.sqrt_nonneg _)
  have hraw' : vaughanMean X Q <=
      (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            ((X : Real) * Real.log (X : Real) ^ 2))) := by
    simpa using hraw.trans (mul_le_mul_of_nonneg_left hmassProduct hcutoff)
  have hsqrtProduct :
      Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            ((X : Real) * Real.log (X : Real) ^ 2)) <=
        81 * Real.sqrt (X : Real) * (Q : Real) ^ 2 * Real.log (X : Real) := by
    apply outerRangeSqrtProduct_le
    · positivity
    · exact_mod_cast hQ
    · exact_mod_cast hXQ
    · exact Real.log_natCast_nonneg X
  let S : Real := vaughanSourceScale X Q
  let L : Real := vaughanLogScale X Q
  have hS : 0 <= S := by dsimp [S, vaughanSourceScale]; positivity
  have hsqrtS : Real.sqrt (X : Real) * (Q : Real) ^ 2 <= S := by
    dsimp [S, vaughanSourceScale]
    have hfirst : 0 <= (X : Real) := by positivity
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    linarith
  have hlogs := outerRangeLogProduct_le
    (sqrtTerm := Real.sqrt (X : Real) * (Q : Real) ^ 2)
    (ell := Real.log (X : Real))
    (ellOne := Real.log ((X : Real) + 1))
    (L := L) (S := S)
    (by simpa [L] using half_le_vaughanLogScale X Q hX hQ)
    (by positivity) (Real.log_natCast_nonneg X)
    (by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= X + 1 by omega)) hS hsqrtS
    (by simpa [L] using log_X_le_vaughanLogScale X Q hX hQ)
    (by simpa [L, Nat.cast_add, Nat.cast_one] using
      log_X_add_one_le_two_vaughanLogScale X Q hX hQ)
  dsimp [S, L] at hlogs
  calc
    vaughanMean X Q <=
        (16 + 4 * Real.log ((X : Real) + 1)) *
          (Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
            Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
              ((X : Real) * Real.log (X : Real) ^ 2))) := hraw'
    _ <= (16 + 4 * Real.log ((X : Real) + 1)) *
        (81 * Real.sqrt (X : Real) * (Q : Real) ^ 2 * Real.log (X : Real)) :=
      mul_le_mul_of_nonneg_left hsqrtProduct hcutoff
    _ <= 6480 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
      simpa [mul_assoc] using hlogs

end BombieriVinogradov.VaughanMeanValue
