import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIISum
import BombieriVinogradov.Assembly.VaughanMeanValue.TypeITwo
import BombieriVinogradov.Definitions.CharacterSums
import Mathlib.Tactic

/-!
# Dyadic blocks for Vaughan's second Type I contribution

The logarithmically bounded factor coefficient is localized to one dyadic
block and passed to the maximal bilinear large-sieve estimate.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

def typeITwoBlockLeftCoefficient (u v M m : Nat) : Complex :=
  if u < m ∧ M < m ∧ m <= 2 * M then
    (typeITwoKernelCoefficient u v m : Complex)
  else 0

def typeITwoRightCoefficient (_ : Nat) : Complex := 1

theorem norm_typeITwoBlockLeftCoefficient_le (u v M m : Nat) :
    ‖typeITwoBlockLeftCoefficient u v M m‖ <=
      Real.log ((2 * M : Nat) : Real) := by
  by_cases hsupport : u < m ∧ M < m ∧ m <= 2 * M
  · rw [typeITwoBlockLeftCoefficient, if_pos hsupport]
    have hlog := typeITwoKernelCoefficient_abs_le_log u v m
    have hlogMono : Real.log (m : Real) <= Real.log ((2 * M : Nat) : Real) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < m by omega)
      · exact_mod_cast hsupport.2.2
    simpa [Complex.norm_real, Real.norm_eq_abs] using hlog.trans hlogMono
  · rw [typeITwoBlockLeftCoefficient, if_neg hsupport, norm_zero]
    simpa using Real.log_natCast_nonneg (2 * M)

theorem typeITwoBlockLeftCoefficient_mass_le (u v M : Nat) :
    coefficientMass (typeITwoBlockLeftCoefficient u v M) (2 * M) <=
      (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by
  unfold coefficientMass
  calc
    ∑ m ∈ Icc 1 (2 * M), ‖typeITwoBlockLeftCoefficient u v M m‖ ^ 2 <=
        ∑ m ∈ Icc 1 (2 * M),
          Real.log ((2 * M : Nat) : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      nlinarith [norm_nonneg (typeITwoBlockLeftCoefficient u v M m),
        norm_typeITwoBlockLeftCoefficient_le u v M m,
        Real.log_natCast_nonneg (2 * M)]
    _ = (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by simp

theorem typeITwoRightCoefficient_mass_le (N : Nat) :
    coefficientMass typeITwoRightCoefficient N <= (N : Real) := by
  unfold coefficientMass typeITwoRightCoefficient
  simp

def typeITwoBlockMean (u v M N X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      maximalBilinearNorm
        (typeITwoBlockLeftCoefficient u v M) typeITwoRightCoefficient
        (2 * M) N X chi

theorem typeITwoBlockMean_le (u v M N X Q : Nat)
    (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoBlockMean u v M N X Q <= typeIIBlockMajorant M N X Q := by
  have hraw := weightedMaximalBilinear_le_cutoffFactor
    X (2 * M) N Q
      (typeITwoBlockLeftCoefficient u v M) typeITwoRightCoefficient hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  unfold typeITwoBlockMean typeIIBlockMajorant
  apply hraw.trans
  have hleft := typeITwoBlockLeftCoefficient_mass_le u v M
  have hright := typeITwoRightCoefficient_mass_le N
  have hleftFactor : 0 <=
      36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) := by positivity
  have hrightFactor : 0 <= 36 * ((N : Real) + (Q : Real) ^ 2) := by positivity
  have hcutoff : 0 <= 16 + 4 * Real.log ((X : Real) + 1) := by
    have : 0 <= Real.log ((X : Real) + 1) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= X + 1 by omega)
    positivity
  have hsqrtLeft :
      Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          coefficientMass (typeITwoBlockLeftCoefficient u v M) (2 * M)) <=
        Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hleft hleftFactor
  have hsqrtRight :
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass typeITwoRightCoefficient N) <=
        Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hright hrightFactor
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hsqrtLeft hsqrtRight (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hcutoff

end BombieriVinogradov.VaughanMeanValue
