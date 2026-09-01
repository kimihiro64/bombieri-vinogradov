import BombieriVinogradov.Assembly.VaughanMeanValue.Bilinear
import BombieriVinogradov.Helpers.LogCutoff.Integer
import Mathlib.Tactic

/-!
# Fourier separation of the bilinear product cutoff

This module transfers the positive natural coefficient convention to the
integer intervals of the character large sieve and proves the exact Fourier
integral representation of `m * n <= Y`.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.LogCutoff

theorem positiveCharacterSum_eq_sum_nat (a : Nat -> Complex) (M q : Nat)
    (chi : DirichletCharacter Complex q) :
    positiveCharacterSum a M q chi =
      ∑ m ∈ Icc 1 M, a m * chi (m : ZMod q) := by
  unfold positiveCharacterSum intervalCharacterSum
  apply Finset.sum_bij (fun n _ => n.toNat)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hnpos : (0 : Int) < n := by omega
    have hnle : n <= (M : Int) := by omega
    simp only [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr fun hzero =>
        (not_le_of_gt hnpos) (Int.toNat_eq_zero.mp hzero)
    · have hcast : (n.toNat : Int) <= (M : Int) := by
        simpa [Int.toNat_of_nonneg hnpos.le] using hnle
      exact_mod_cast hcast
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    have hn₁pos : (0 : Int) < n₁ := by omega
    have hn₂pos : (0 : Int) < n₂ := by omega
    calc
      n₁ = (n₁.toNat : Int) := (Int.toNat_of_nonneg hn₁pos.le).symm
      _ = (n₂.toNat : Int) := by exact_mod_cast heq
      _ = n₂ := Int.toNat_of_nonneg hn₂pos.le
  · intro m hm
    refine ⟨(m : Int), ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      constructor
      · exact_mod_cast (show 0 < m from (Finset.mem_Icc.mp hm).1)
      · simpa using (show (m : Int) <= (M : Int) by
          exact_mod_cast (Finset.mem_Icc.mp hm).2)
    · simp
  · intro n hn
    have hnpos : (0 : Int) <= n := by
      have := Finset.mem_Ioc.mp hn
      omega
    rw [show n = (n.toNat : Int) by exact (Int.toNat_of_nonneg hnpos).symm]
    simp [positiveIntervalCoefficients]

theorem positiveCoefficientMass_eq_coefficientMass (a : Nat -> Complex) (M : Nat) :
    positiveCoefficientMass a M = coefficientMass a M := by
  unfold positiveCoefficientMass coefficientMass
  apply Finset.sum_bij (fun n _ => n.toNat)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hnpos : (0 : Int) < n := by omega
    have hnle : n <= (M : Int) := by omega
    simp only [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr fun hzero =>
        (not_le_of_gt hnpos) (Int.toNat_eq_zero.mp hzero)
    · have hcast : (n.toNat : Int) <= (M : Int) := by
        simpa [Int.toNat_of_nonneg hnpos.le] using hnle
      exact_mod_cast hcast
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    have hn₁pos : (0 : Int) < n₁ := by omega
    have hn₂pos : (0 : Int) < n₂ := by omega
    calc
      n₁ = (n₁.toNat : Int) := (Int.toNat_of_nonneg hn₁pos.le).symm
      _ = (n₂.toNat : Int) := by exact_mod_cast heq
      _ = n₂ := Int.toNat_of_nonneg hn₂pos.le
  · intro m hm
    refine ⟨(m : Int), ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      constructor
      · exact_mod_cast (show 0 < m from (Finset.mem_Icc.mp hm).1)
      · simpa using (show (m : Int) <= (M : Int) by
          exact_mod_cast (Finset.mem_Icc.mp hm).2)
    · simp
  · intro n hn
    simp [positiveIntervalCoefficients]

def fourierTwist (xi : Real) (a : Nat -> Complex) (m : Nat) : Complex :=
  Real.fourierChar (xi * Real.log (m : Real)) • a m

theorem norm_fourierTwist (xi : Real) (a : Nat -> Complex) (m : Nat) :
    ‖fourierTwist xi a m‖ = ‖a m‖ := by
  simp [fourierTwist, Circle.norm_smul]

theorem coefficientMass_fourierTwist (xi : Real) (a : Nat -> Complex) (M : Nat) :
    coefficientMass (fourierTwist xi a) M = coefficientMass a M := by
  simp [coefficientMass, norm_fourierTwist]

theorem positiveCoefficientMass_fourierTwist
    (xi : Real) (a : Nat -> Complex) (M : Nat) :
    positiveCoefficientMass (fourierTwist xi a) M = positiveCoefficientMass a M := by
  rw [positiveCoefficientMass_eq_coefficientMass,
    coefficientMass_fourierTwist,
    positiveCoefficientMass_eq_coefficientMass]

theorem fourierChar_log_mul (xi : Real) (m n : Nat)
    (hm : 1 <= m) (hn : 1 <= n) :
    Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) =
      Real.fourierChar (xi * Real.log (m : Real)) *
        Real.fourierChar (xi * Real.log (n : Real)) := by
  have hm0 : Ne (m : Real) 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hn0 : Ne (n : Real) 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  push_cast
  rw [Real.log_mul hm0 hn0]
  rw [mul_add, AddChar.map_add_eq_mul]

theorem bilinearCharacterProduct_fourierTwist (xi : Real)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b) M N q chi =
      ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
          (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
  rw [bilinearCharacterProduct, positiveCharacterSum_eq_sum_nat,
    positiveCharacterSum_eq_sum_nat]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hm1 : 1 <= m := (Finset.mem_Icc.mp hm).1
  have hn1 : 1 <= n := (Finset.mem_Icc.mp hn).1
  have hchi : chi ((m * n : Nat) : ZMod q) =
      chi (m : ZMod q) * chi (n : ZMod q) := by
    rw [show ((m * n : Nat) : ZMod q) = (m : ZMod q) * (n : ZMod q) by
      push_cast
      rfl]
    exact map_mul chi _ _
  rw [fourierChar_log_mul xi m n hm1 hn1]
  simp only [fourierTwist, Circle.smul_def, hchi, Circle.coe_mul]
  ring

theorem fourierCutoffTerm_integrable (Y k : Nat) (hY : 1 <= Y)
    (c : Complex) :
    Integrable (fun xi : Real =>
      (Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi) * c) := by
  have hcontinuous : Continuous (fun xi : Real =>
      Real.fourierChar (xi * Real.log (k : Real))) := by
    fun_prop
  have hfourier := fourier_integerLogCutoff_integrable Y hY
  have hproduct : Integrable (fun xi : Real =>
      Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi) := by
    simp_rw [← integrable_norm_iff
      (hcontinuous.aestronglyMeasurable.fun_smul hfourier.1),
      Circle.norm_smul]
    exact hfourier.norm
  exact hproduct.mul_const c

theorem restrictedBilinearCharacterSum_fourier (a b : Nat -> Complex)
    (M N Y q : Nat) (chi : DirichletCharacter Complex q) (hY : 1 <= Y) :
    restrictedBilinearCharacterSum a b M N Y q chi =
      ∫ xi : Real, 𝓕 (integerLogCutoff Y) xi *
        bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi := by
  rw [restrictedBilinearCharacterSum]
  calc
    (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        if m * n <= Y then a m * b n * chi ((m * n : Nat) : ZMod q) else 0) =
        ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          (if m * n <= Y then 1 else 0 : Complex) *
            (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          (∫ xi : Real,
            Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
              𝓕 (integerLogCutoff Y) xi) *
            (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [integerIndicator_fourier_representation Y (m * n) hY]
      exact Nat.mul_pos (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hm).1)
        (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1)
    _ = ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          ∫ xi : Real,
            (Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
              𝓕 (integerLogCutoff Y) xi) *
              (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      simp_rw [integral_mul_const]
    _ = ∫ xi : Real, ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          (Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
            𝓕 (integerLogCutoff Y) xi) *
            (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      rw [integral_finsetSum]
      · congr 1
        funext m
        rw [integral_finsetSum]
        intro n hn
        exact fourierCutoffTerm_integrable Y (m * n) hY _
      · intro m hm
        exact integrable_finsetSum (Icc 1 N) (fun n hn =>
          fourierCutoffTerm_integrable Y (m * n) hY _)
    _ = ∫ xi : Real, 𝓕 (integerLogCutoff Y) xi *
        bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi := by
      apply integral_congr_ae
      filter_upwards with xi
      rw [bilinearCharacterProduct_fourierTwist]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Circle.smul_def]
      ring

end BombieriVinogradov.VaughanMeanValue
