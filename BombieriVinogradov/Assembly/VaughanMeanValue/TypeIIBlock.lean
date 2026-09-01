import BombieriVinogradov.Assembly.VaughanMeanValue.Hyperbola
import BombieriVinogradov.Assembly.VaughanMeanValue.MaximalBilinear
import BombieriVinogradov.Proof.VaughanIdentity.Kernel

/-!
# One dyadic Type II block

The corrected Vaughan Type II kernel is reindexed over its two factors. Its
von-Mangoldt divisor-tail and Moebius-tail coefficient masses are bounded
explicitly, then passed to the maximal bilinear character large sieve.
-/


set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity

def typeIILeftKernelCoefficient (u m : Nat) : Real :=
  ∑ factors ∈ Nat.divisorsAntidiagonal m,
    (if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1) *
      ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2)

def typeIIBlockLeftCoefficient (u M m : Nat) : Complex :=
  if M < m ∧ m <= 2 * M then (typeIILeftKernelCoefficient u m : Complex) else 0

def typeIIRightCoefficient (v n : Nat) : Complex :=
  if n <= v then 0 else
    (((ArithmeticFunction.moebius : ArithmeticFunction Real) n : Real) : Complex)

theorem typeIILeftKernelCoefficient_nonneg (u m : Nat) :
    0 <= typeIILeftKernelCoefficient u m := by
  unfold typeIILeftKernelCoefficient
  apply Finset.sum_nonneg
  intro factors hfactors
  have hright : Ne factors.2 0 :=
    Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors
  by_cases hcutoff : factors.1 <= u
  · simp [hcutoff]
  · simp [hcutoff, ArithmeticFunction.zeta_apply_ne hright,
      ArithmeticFunction.vonMangoldt_nonneg]

theorem typeIILeftKernelCoefficient_le_log (u m : Nat) :
    typeIILeftKernelCoefficient u m <= Real.log (m : Real) := by
  calc
    typeIILeftKernelCoefficient u m <=
        ∑ factors ∈ Nat.divisorsAntidiagonal m,
          ArithmeticFunction.vonMangoldt factors.1 *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2) := by
      unfold typeIILeftKernelCoefficient
      apply Finset.sum_le_sum
      intro factors hfactors
      have hright : Ne factors.2 0 :=
        Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors
      by_cases hcutoff : factors.1 <= u
      · simp [hcutoff, ArithmeticFunction.zeta_apply_ne hright,
          ArithmeticFunction.vonMangoldt_nonneg]
      · simp [hcutoff]
    _ = (ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction Real)) m := by
      rw [ArithmeticFunction.mul_apply]
    _ = Real.log (m : Real) := by
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      rfl

theorem typeIIKernel_apply_coefficients (u v n : Nat) :
    typeIIKernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        typeIILeftKernelCoefficient u pair.1 *
          (if pair.2 <= v then 0 else
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) := by
  rw [typeIIKernel_apply]
  rfl

def typeIICharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 Y, ∑ n ∈ Icc 1 (Y / m),
    (typeIILeftKernelCoefficient u m : Complex) * typeIIRightCoefficient v n *
      chi ((m * n : Nat) : ZMod q)

theorem vaughanS3_eq_typeIICharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    vaughanS3 u v Y (fun n => chi (n : ZMod q)) =
      typeIICharacterSum u v Y q chi := by
  unfold vaughanS3 weightedKernelSum
  simp_rw [typeIIKernel_apply_coefficients]
  push_cast
  simp_rw [Finset.sum_mul]
  have hreindex :
      (∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
        (typeIILeftKernelCoefficient u pair.1 : Complex) *
          (((if pair.2 <= v then 0 else
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) : Real) : Complex) *
              chi (k : ZMod q)) =
        ∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
          (typeIILeftKernelCoefficient u pair.1 : Complex) *
            (((if pair.2 <= v then 0 else
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) : Real) : Complex) *
                chi ((pair.1 * pair.2 : Nat) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro pair hpair
    rw [(Nat.mem_divisorsAntidiagonal.mp hpair).1]
  rw [hreindex]
  have hhyper := sum_divisorsAntidiagonal_Icc_eq_hyperbola
    (fun m n =>
      (typeIILeftKernelCoefficient u m : Complex) *
        (((if n <= v then 0 else
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) n)) : Real) : Complex) *
            chi ((m * n : Nat) : ZMod q)) Y
  rw [hhyper]
  unfold typeIICharacterSum typeIIRightCoefficient
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcutoff : n <= v <;> simp [hcutoff]

theorem norm_typeIIBlockLeftCoefficient_le (u M m : Nat) :
    ‖typeIIBlockLeftCoefficient u M m‖ <= Real.log ((2 * M : Nat) : Real) := by
  by_cases hsupport : M < m ∧ m <= 2 * M
  · rw [typeIIBlockLeftCoefficient, if_pos hsupport]
    have hnonneg := typeIILeftKernelCoefficient_nonneg u m
    have hlog := typeIILeftKernelCoefficient_le_log u m
    have hlogMono : Real.log (m : Real) <= Real.log ((2 * M : Nat) : Real) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < m by omega)
      · exact_mod_cast hsupport.2
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hlog.trans hlogMono
  · rw [typeIIBlockLeftCoefficient, if_neg hsupport, norm_zero]
    simpa using Real.log_natCast_nonneg (2 * M)

theorem typeIIBlockLeftCoefficient_mass_le (u M : Nat) :
    coefficientMass (typeIIBlockLeftCoefficient u M) (2 * M) <=
      (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by
  unfold coefficientMass
  have hlog : 0 <= Real.log ((2 * M : Nat) : Real) :=
    Real.log_natCast_nonneg (2 * M)
  calc
    ∑ m ∈ Icc 1 (2 * M), ‖typeIIBlockLeftCoefficient u M m‖ ^ 2 <=
        ∑ m ∈ Icc 1 (2 * M),
          Real.log ((2 * M : Nat) : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      nlinarith [norm_nonneg (typeIIBlockLeftCoefficient u M m),
        norm_typeIIBlockLeftCoefficient_le u M m]
    _ = (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by simp

theorem norm_typeIIRightCoefficient_le_one (v n : Nat) :
    ‖typeIIRightCoefficient v n‖ <= 1 := by
  by_cases hcutoff : n <= v
  · simp [typeIIRightCoefficient, hcutoff]
  · rw [typeIIRightCoefficient, if_neg hcutoff]
    rcases ArithmeticFunction.moebius_eq_or n with hzero | hone | hneg
    · simp [hzero]
    · simp [hone]
    · simp [hneg]

theorem typeIIRightCoefficient_mass_le (v N : Nat) :
    coefficientMass (typeIIRightCoefficient v) N <= (N : Real) := by
  unfold coefficientMass
  calc
    ∑ n ∈ Icc 1 N, ‖typeIIRightCoefficient v n‖ ^ 2 <=
        ∑ n ∈ Icc 1 N, (1 : Real) := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [norm_nonneg (typeIIRightCoefficient v n),
        norm_typeIIRightCoefficient_le_one v n]
    _ = (N : Real) := by simp

def typeIIBlockMean (u v M N X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      maximalBilinearNorm
        (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v)
        (2 * M) N X chi

theorem typeIIBlockMean_le (u v M N X Q : Nat)
    (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIBlockMean u v M N X Q <=
      (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
            (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real))) := by
  have hraw := weightedMaximalBilinear_le_cutoffFactor
    X (2 * M) N Q
      (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v) hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  unfold typeIIBlockMean
  apply hraw.trans
  have hleft := typeIIBlockLeftCoefficient_mass_le u M
  have hright := typeIIRightCoefficient_mass_le v N
  have hleftFactor : 0 <=
      36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) := by positivity
  have hrightFactor : 0 <= 36 * ((N : Real) + (Q : Real) ^ 2) := by positivity
  have hcutoff : 0 <= 16 + 4 * Real.log ((X : Real) + 1) := by
    have : 0 <= Real.log ((X : Real) + 1) := by
      apply Real.log_nonneg
      have hnat : 1 <= X + 1 := by omega
      exact_mod_cast hnat
    positivity
  have hsqrtLeft :
      Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          coefficientMass (typeIIBlockLeftCoefficient u M) (2 * M)) <=
        Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hleft hleftFactor
  have hsqrtRight :
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass (typeIIRightCoefficient v) N) <=
        Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hright hrightFactor
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hsqrtLeft hsqrtRight (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hcutoff

end BombieriVinogradov.VaughanMeanValue
