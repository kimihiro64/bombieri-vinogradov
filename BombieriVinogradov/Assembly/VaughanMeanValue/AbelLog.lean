import BombieriVinogradov.Assembly.VaughanMeanValue.FourierBridge
import BombieriVinogradov.Assembly.VaughanMeanValue.PolyaVinogradov
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-!
# Logarithmically weighted primitive-character prefixes

Discrete Abel summation transfers the Pólya-Vinogradov prefix estimate to
logarithmic weights with one additional logarithmic factor.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

def logWeightedCharacterPrefix (L q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Icc 1 L, (Real.log (n : Real) : Complex) * chi (n : ZMod q)

theorem intervalCharacterSum_one_eq_sum_range (N q : Nat)
    (chi : DirichletCharacter Complex q) :
    intervalCharacterSum oneIntegerCoefficient 0 N q chi =
      ∑ i ∈ range N, chi ((i + 1 : Nat) : ZMod q) := by
  calc
    intervalCharacterSum oneIntegerCoefficient 0 N q chi =
        positiveCharacterSum (fun _ : Nat => (1 : Complex)) N q chi := by
      rfl
    _ = ∑ n ∈ Icc 1 N, chi (n : ZMod q) := by
      rw [positiveCharacterSum_eq_sum_nat]
      simp
    _ = ∑ i ∈ range N, chi ((i + 1 : Nat) : ZMod q) := by
      apply Finset.sum_bij (fun n _ => n - 1)
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        simp only [Finset.mem_range]
        omega
      · intro n₁ hn₁ n₂ hn₂ heq
        simp only [Finset.mem_Icc] at hn₁ hn₂
        omega
      · intro i hi
        refine ⟨i + 1, ?_, ?_⟩
        · simp only [Finset.mem_Icc, Nat.one_le_iff_ne_zero, ne_eq]
          constructor
          · omega
          · exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
        · omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        congr 2
        omega

theorem logWeightedCharacterPrefix_eq_sum_range (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    logWeightedCharacterPrefix L q chi =
      ∑ i ∈ range L,
        (Real.log ((i + 1 : Nat) : Real) : Complex) *
          chi ((i + 1 : Nat) : ZMod q) := by
  unfold logWeightedCharacterPrefix
  apply Finset.sum_bij (fun n _ => n - 1)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Icc] at hn₁ hn₂
    omega
  · intro i hi
    have hil : i < L := Finset.mem_range.mp hi
    refine ⟨i + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have hback : n - 1 + 1 = n := Nat.sub_add_cancel hn.1
    rw [hback]

theorem logWeightedCharacterPrefix_by_parts (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    logWeightedCharacterPrefix L q chi =
      (Real.log (L : Real) : Complex) *
          intervalCharacterSum oneIntegerCoefficient 0 L q chi -
        ∑ i ∈ range (L - 1),
          (Real.log ((i + 2 : Nat) : Real) -
              Real.log ((i + 1 : Nat) : Real) : Real) •
            intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi := by
  by_cases hL : L = 0
  · simp [hL, logWeightedCharacterPrefix, intervalCharacterSum]
  rw [logWeightedCharacterPrefix_eq_sum_range]
  change (∑ i ∈ range L,
      Real.log ((i + 1 : Nat) : Real) • chi ((i + 1 : Nat) : ZMod q)) = _
  change _ = Real.log (L : Real) •
      intervalCharacterSum oneIntegerCoefficient 0 L q chi - _
  have hparts := Finset.sum_range_by_parts
    (fun i : Nat => Real.log ((i + 1 : Nat) : Real))
    (fun i : Nat => chi ((i + 1 : Nat) : ZMod q)) L
  rw [hparts]
  simp_rw [← intervalCharacterSum_one_eq_sum_range]
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  rw [Nat.sub_add_cancel hLpos]

theorem sum_log_successive_differences (K : Nat) :
    ∑ i ∈ range K,
        (Real.log ((i + 2 : Nat) : Real) -
          Real.log ((i + 1 : Nat) : Real)) =
      Real.log ((K + 1 : Nat) : Real) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem log_successive_difference_nonneg (i : Nat) :
    0 <= Real.log ((i + 2 : Nat) : Real) -
      Real.log ((i + 1 : Nat) : Real) := by
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · positivity
  · exact_mod_cast (show i + 1 <= i + 2 by omega)

theorem norm_logWeightedCharacterPrefix_le_of_prefix_bound
    (L q : Nat) (chi : DirichletCharacter Complex q) (B : Real)
    (hB : 0 <= B)
    (hprefix : ∀ k, k <= L ->
      ‖intervalCharacterSum oneIntegerCoefficient 0 k q chi‖ <= B) :
    ‖logWeightedCharacterPrefix L q chi‖ <=
      2 * B * Real.log ((L + 1 : Nat) : Real) := by
  by_cases hL : L = 0
  · simp [hL, logWeightedCharacterPrefix]
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  have hlogL : 0 <= Real.log (L : Real) := Real.log_natCast_nonneg L
  have hmain :
      ‖logWeightedCharacterPrefix L q chi‖ <=
        Real.log (L : Real) * B + Real.log (L : Real) * B := by
    rw [logWeightedCharacterPrefix_by_parts]
    calc
      ‖(Real.log (L : Real) : Complex) *
            intervalCharacterSum oneIntegerCoefficient 0 L q chi -
          ∑ i ∈ range (L - 1),
            (Real.log ((i + 2 : Nat) : Real) -
                Real.log ((i + 1 : Nat) : Real) : Real) •
              intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ <=
          ‖(Real.log (L : Real) : Complex) *
              intervalCharacterSum oneIntegerCoefficient 0 L q chi‖ +
            ‖∑ i ∈ range (L - 1),
              (Real.log ((i + 2 : Nat) : Real) -
                  Real.log ((i + 1 : Nat) : Real) : Real) •
                intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ :=
        norm_sub_le _ _
      _ <= Real.log (L : Real) * B +
          ∑ i ∈ range (L - 1),
            (Real.log ((i + 2 : Nat) : Real) -
              Real.log ((i + 1 : Nat) : Real)) * B := by
        apply add_le_add
        · rw [norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogL]
          exact mul_le_mul_of_nonneg_left (hprefix L le_rfl) hlogL
        · calc
            ‖∑ i ∈ range (L - 1),
                (Real.log ((i + 2 : Nat) : Real) -
                    Real.log ((i + 1 : Nat) : Real) : Real) •
                  intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ <=
                ∑ i ∈ range (L - 1),
                  ‖(Real.log ((i + 2 : Nat) : Real) -
                      Real.log ((i + 1 : Nat) : Real) : Real) •
                    intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ :=
              norm_sum_le _ _
            _ <= ∑ i ∈ range (L - 1),
                (Real.log ((i + 2 : Nat) : Real) -
                  Real.log ((i + 1 : Nat) : Real)) * B := by
              apply Finset.sum_le_sum
              intro i hi
              have hiL : i + 1 <= L := by
                have hirange := Finset.mem_range.mp hi
                omega
              rw [norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (log_successive_difference_nonneg i)]
              exact mul_le_mul_of_nonneg_left (hprefix (i + 1) hiL)
                (log_successive_difference_nonneg i)
      _ = Real.log (L : Real) * B + Real.log (L : Real) * B := by
        rw [← Finset.sum_mul, sum_log_successive_differences]
        rw [Nat.sub_add_cancel hLpos]
  have hlogMono : Real.log (L : Real) <=
      Real.log ((L + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hLpos
    · exact_mod_cast (show L <= L + 1 by omega)
  calc
    ‖logWeightedCharacterPrefix L q chi‖ <=
        Real.log (L : Real) * B + Real.log (L : Real) * B := hmain
    _ = 2 * B * Real.log (L : Real) := by ring
    _ <= 2 * B * Real.log ((L + 1 : Nat) : Real) := by
      exact mul_le_mul_of_nonneg_left hlogMono (by positivity)

theorem norm_logWeightedCharacterPrefix_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (L : Nat) :
    ‖logWeightedCharacterPrefix L q chi‖ <=
      4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
        Real.log ((L + 1 : Nat) : Real) := by
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  have hbound := norm_logWeightedCharacterPrefix_le_of_prefix_bound
    L q chi (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)))
    (by positivity) (fun k hk => polyaVinogradov hq hchi 0 k)
  convert hbound using 1
  all_goals ring

theorem norm_logWeightedCharacterPrefix_trivial (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖logWeightedCharacterPrefix L q chi‖ <=
      (L : Real) * Real.log ((L + 1 : Nat) : Real) := by
  unfold logWeightedCharacterPrefix
  calc
    ‖∑ n ∈ Icc 1 L,
        (Real.log (n : Real) : Complex) * chi (n : ZMod q)‖ <=
        ∑ n ∈ Icc 1 L,
          ‖(Real.log (n : Real) : Complex) * chi (n : ZMod q)‖ :=
      norm_sum_le _ _
    _ <= ∑ n ∈ Icc 1 L,
        Real.log ((L + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnBounds := Finset.mem_Icc.mp hn
      have hlogn : 0 <= Real.log (n : Real) := Real.log_natCast_nonneg n
      have hlog : Real.log (n : Real) <=
          Real.log ((L + 1 : Nat) : Real) := by
        apply Real.log_le_log
        · exact_mod_cast (show 0 < n by omega)
        · exact_mod_cast (show n <= L + 1 by omega)
      calc
        ‖(Real.log (n : Real) : Complex) * chi (n : ZMod q)‖ =
            Real.log (n : Real) * ‖chi (n : ZMod q)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn]
        _ <= Real.log (n : Real) * 1 := by
          exact mul_le_mul_of_nonneg_left
            (DirichletCharacter.norm_le_one chi (n : ZMod q)) hlogn
        _ <= Real.log ((L + 1 : Nat) : Real) := by simpa using hlog
    _ = (L : Real) * Real.log ((L + 1 : Nat) : Real) := by simp

end BombieriVinogradov.VaughanMeanValue
