import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIOne
import BombieriVinogradov.Assembly.VaughanMeanValue.TypeITwoSum
import Mathlib.Tactic

/-!
# Hybrid mean-value estimate for Vaughan's second Type I contribution

The small-factor range uses Pólya–Vinogradov, while the complementary range
uses the maximal dyadic bilinear estimate with the coefficient support bound.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity

theorem norm_intervalCharacterSum_one_le (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖intervalCharacterSum oneIntegerCoefficient 0 L q chi‖ <= (L : Real) := by
  rw [intervalCharacterSum_one_eq_Icc]
  calc
    _ <= ∑ n ∈ Icc 1 L, ‖chi (n : ZMod q)‖ := norm_sum_le _ _
    _ <= ∑ n ∈ Icc 1 L, (1 : Real) := by
      apply Finset.sum_le_sum
      intro n hn
      exact DirichletCharacter.norm_le_one chi (n : ZMod q)
    _ = (L : Real) := by simp

theorem norm_typeITwoSmallCharacterSum_trivial (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖typeITwoSmallCharacterSum u v Y q chi‖ <=
      3 * (Y : Real) * Real.log ((Y + 1 : Nat) : Real) ^ 2 := by
  let active : Finset Nat := (Icc 1 Y).filter fun m => m <= u
  have hterm : ∀ m ∈ active,
      ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ <=
        (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hmData.1).1
    have hcoeff : ‖(typeITwoKernelCoefficient u v m : Complex)‖ <=
        Real.log ((Y + 1 : Nat) : Real) := by
      calc
        ‖(typeITwoKernelCoefficient u v m : Complex)‖ =
            |typeITwoKernelCoefficient u v m| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ <= Real.log (m : Real) := typeITwoKernelCoefficient_abs_le_log u v m
        _ <= Real.log ((Y + 1 : Nat) : Real) := by
          apply Real.log_le_log
          · exact_mod_cast hmpos
          · exact_mod_cast Nat.le_succ_of_le (Finset.mem_Icc.mp hmData.1).2
    rw [typeITwoInnerSum_eq_prefix, norm_mul, norm_mul]
    have hprefix := norm_intervalCharacterSum_one_le (Y / m) q chi
    have hfloor : ((Y / m : Nat) : Real) <= (Y : Real) / (m : Real) :=
      Nat.cast_div_le
    calc
      _ <= Real.log ((Y + 1 : Nat) : Real) * 1 * ((Y / m : Nat) : Real) := by
        gcongr
        exact DirichletCharacter.norm_le_one chi (m : ZMod q)
      _ <= Real.log ((Y + 1 : Nat) : Real) * 1 *
          ((Y : Real) / (m : Real)) := by gcongr
      _ = (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) := by
        rw [div_eq_mul_inv]
        ring
  have hactive : active ⊆ Icc 1 Y := fun m hm => (Finset.mem_filter.mp hm).1
  have hharmonic : ∑ m ∈ Icc 1 Y, (m : Real)⁻¹ = (harmonic Y : Real) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  unfold typeITwoSmallCharacterSum
  change ‖∑ m ∈ active, ∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)‖ <= _
  calc
    _ <= ∑ m ∈ active, ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ := norm_sum_le _ _
    _ <= ∑ m ∈ active,
        (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) :=
      Finset.sum_le_sum hterm
    _ <= ∑ m ∈ Icc 1 Y,
        (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hactive
      intro m hmAll hmActive
      positivity
    _ = (Y : Real) * (harmonic Y : Real) *
        Real.log ((Y + 1 : Nat) : Real) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hharmonic]
    _ <= (Y : Real) * (3 * Real.log ((Y + 1 : Nat) : Real)) *
        Real.log ((Y + 1 : Nat) : Real) := by
      gcongr
      exact harmonic_le_three_log_add_one Y
    _ = 3 * (Y : Real) * Real.log ((Y + 1 : Nat) : Real) ^ 2 := by ring

def maximalTypeITwoSmallCharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖typeITwoSmallCharacterSum u v Y q chi‖

theorem maximalTypeITwoSmallCharacterNorm_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (u v X : Nat) :
    maximalTypeITwoSmallCharacterNorm u v X q chi <=
      (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
  unfold maximalTypeITwoSmallCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  exact norm_typeITwoSmallCharacterSum_le hq hchi u v Y

def typeITwoSmallMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi

theorem maximalTypeITwoSmallCharacterNorm_trivial (u v X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalTypeITwoSmallCharacterNorm u v X q chi <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
  unfold maximalTypeITwoSmallCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  have hbase := norm_typeITwoSmallCharacterSum_trivial u v Y q chi
  apply hbase.trans
  have hlog : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_right hYX 1
  have hlogY : 0 <= Real.log ((Y + 1 : Nat) : Real) :=
    Real.log_natCast_nonneg (Y + 1)
  have hlogX : 0 <= Real.log ((X + 1 : Nat) : Real) :=
    Real.log_natCast_nonneg (X + 1)
  gcongr

theorem weighted_primitive_typeITwoSmall_le {q : Nat} [NeZero q]
    (hq : 1 < q) (u v X : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi <=
      (q : Real) * (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
  classical
  let B : Real := (u : Real) *
    (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
      Real.log (2 * (q : Real)))
  have hB : 0 <= B := by
    dsimp [B]
    have hlogu := Real.log_natCast_nonneg u
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
      linarith
    positivity
  have hchars :
      ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi <=
        (q.totient : Real) * B := by
    calc
      _ <= ∑ chi ∈ primitiveCharacters q, B := by
        apply Finset.sum_le_sum
        intro chi hchiMem
        have hchi : DirichletCharacter.IsPrimitive chi := by
          simpa [primitiveCharacters] using (Finset.mem_filter.mp hchiMem).2
        exact maximalTypeITwoSmallCharacterNorm_le hq hchi u v X
      _ = ((primitiveCharacters q).card : Real) * B := by simp
      _ <= (q.totient : Real) * B := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast primitiveCharacters_card_le_totient q) hB
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    _ <= ((q : Real) / (q.totient : Real)) * ((q.totient : Real) * B) :=
      mul_le_mul_of_nonneg_left hchars (by positivity)
    _ = (q : Real) * B := by field_simp
    _ = _ := by dsimp [B]; ring

def nontrivialTypeITwoSmallMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi

theorem nontrivialTypeITwoSmallMean_le (u v X Q : Nat) :
    nontrivialTypeITwoSmallMean u v X Q <=
      2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
        Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) := by
  let D : Real := (Q : Real) * (u : Real) *
    (2 * Real.log (u : Real) * Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)))
  have hD : 0 <= D := by
    dsimp [D]
    have hlogu := Real.log_natCast_nonneg u
    by_cases hQ : Q = 0
    · simp [hQ]
    · have hlogQ : 0 <= Real.log (2 * (Q : Real)) := by
        apply Real.log_nonneg
        have : (1 : Real) <= (Q : Real) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
        linarith
      positivity
  have hterm : ∀ q ∈ Icc 2 Q,
      ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi <= D := by
    intro q hqMem
    have hqBounds := Finset.mem_Icc.mp hqMem
    let _ : NeZero q := ⟨(by omega)⟩
    apply (weighted_primitive_typeITwoSmall_le (show 1 < q by omega) u v X).trans
    dsimp [D]
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast (show 1 <= q by omega)
      linarith
    have hqcast : (q : Real) <= (Q : Real) := by exact_mod_cast hqBounds.2
    have hsqrt : Real.sqrt (q : Real) <= Real.sqrt (Q : Real) :=
      Real.sqrt_le_sqrt hqcast
    have hlog : Real.log (2 * (q : Real)) <= Real.log (2 * (Q : Real)) := by
      apply Real.log_le_log
      · exact mul_pos (by norm_num) (by exact_mod_cast (show 0 < q by omega))
      · nlinarith
    gcongr
  unfold nontrivialTypeITwoSmallMean
  calc
    _ <= ∑ q ∈ Icc 2 Q, D := Finset.sum_le_sum hterm
    _ = ((Icc 2 Q).card : Real) * D := by simp
    _ <= (Q : Real) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show (Icc 2 Q).card <= Q by simp)
    _ = _ := by dsimp [D]; ring

theorem typeITwoSmallMean_le (u v X Q : Nat) (hQ : 1 <= Q) :
    typeITwoSmallMean u v X Q <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
          Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) := by
  have hlevel :
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1,
            maximalTypeITwoSmallCharacterNorm u v X 1 chi <=
        3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
    let B : Real := 3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2
    have hB : 0 <= B := by dsimp [B]; positivity
    have hsum : ∑ chi ∈ primitiveCharacters 1,
        maximalTypeITwoSmallCharacterNorm u v X 1 chi <= B := by
      calc
        _ <= ∑ chi ∈ primitiveCharacters 1, B := by
          apply Finset.sum_le_sum
          intro chi hchi
          exact maximalTypeITwoSmallCharacterNorm_trivial u v X 1 chi
        _ = ((primitiveCharacters 1).card : Real) * B := by simp
        _ <= B := by
          have hcard : ((primitiveCharacters 1).card : Real) <= 1 := by
            exact_mod_cast primitiveCharacters_card_le_totient 1
          nlinarith
    norm_num
    simpa [B] using hsum
  have hsplit : typeITwoSmallMean u v X Q =
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1,
            maximalTypeITwoSmallCharacterNorm u v X 1 chi +
        nontrivialTypeITwoSmallMean u v X Q := by
    unfold typeITwoSmallMean nontrivialTypeITwoSmallMean
    rw [← Finset.insert_Icc_succ_left_eq_Icc hQ]
    rw [Finset.sum_insert (by simp)]
    simp
  rw [hsplit]
  exact add_le_add hlevel (nontrivialTypeITwoSmallMean_le u v X Q)

def maximalTypeITwoCharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS2 u v Y (fun n => chi (n : ZMod q))‖

theorem maximalTypeITwoCharacterNorm_le (u v X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalTypeITwoCharacterNorm u v X q chi <=
      maximalTypeITwoSmallCharacterNorm u v X q chi +
        maximalTypeITwoLargeCharacterNorm u v X q chi := by
  unfold maximalTypeITwoCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  rw [vaughanS2_eq_typeITwoCharacterSum,
    typeITwoCharacterSum_eq_small_add_large]
  calc
    _ <= ‖typeITwoSmallCharacterSum u v Y q chi‖ +
        ‖typeITwoLargeCharacterSum u v Y q chi‖ := norm_add_le _ _
    _ <= maximalTypeITwoSmallCharacterNorm u v X q chi +
        maximalTypeITwoLargeCharacterNorm u v X q chi := by
      apply add_le_add
      · unfold maximalTypeITwoSmallCharacterNorm
        exact Finset.le_sup'
          (fun Z => ‖typeITwoSmallCharacterSum u v Z q chi‖) hY
      · unfold maximalTypeITwoLargeCharacterNorm
        exact Finset.le_sup'
          (fun Z => ‖typeITwoLargeCharacterSum u v Z q chi‖) hY

def typeITwoMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoCharacterNorm u v X q chi

theorem typeITwoMean_le_hybrid
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoMean u u X Q <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
          Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) +
        11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q := by
  have hsplit : typeITwoMean u u X Q <=
      typeITwoSmallMean u u X Q + typeITwoLargeMean u u X Q := by
    unfold typeITwoMean typeITwoSmallMean typeITwoLargeMean
    calc
      _ <= ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            (maximalTypeITwoSmallCharacterNorm u u X q chi +
              maximalTypeITwoLargeCharacterNorm u u X q chi) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro chi hchi
          exact maximalTypeITwoCharacterNorm_le u u X q chi
        · positivity
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
  exact hsplit.trans (add_le_add (typeITwoSmallMean_le u u X Q hQ)
    (typeITwoLargeMean_le_sourceScale u X Q hu hX hQ))

end BombieriVinogradov.VaughanMeanValue
