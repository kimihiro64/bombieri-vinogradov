import BombieriVinogradov.Assembly.VaughanMeanValue.TypeITwoDyadic
import Mathlib.Tactic

/-!
# Source-scale estimate for the large part of Vaughan's second Type I term

Only the left factor is bounded below by the cutoff. Its upper support at
`u * v` supplies the complementary square-root estimate hidden by the source's
brief comparison with the Type II term.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

def typeITwoLargeMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoLargeCharacterNorm u v X q chi

theorem typeITwoLargeMean_le_sum_blockMeans
    (u v X Q : Nat) (hu : 1 <= u) :
    typeITwoLargeMean u v X Q <=
      ∑ k ∈ dyadicExponentSet X,
        typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
  unfold typeITwoLargeMean
  calc
    _ <= ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, ∑ k ∈ dyadicExponentSet X,
          maximalBilinearNorm
            (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
            (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalTypeITwoLargeCharacterNorm_le_sum_blocks u v X q chi hu
      · positivity
    _ = ∑ k ∈ dyadicExponentSet X,
        typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      unfold typeITwoBlockMean
      let F : (q : Nat) -> DirichletCharacter Complex q -> Nat -> Real :=
        fun q chi k => maximalBilinearNorm
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) X chi
      change (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, ∑ k ∈ dyadicExponentSet X, F q chi k) =
        ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
          ((q : Real) / (q.totient : Real)) *
            ∑ chi ∈ primitiveCharacters q, F q chi k
      calc
        _ = ∑ q ∈ Icc 1 Q, ∑ chi ∈ primitiveCharacters q,
            ∑ k ∈ dyadicExponentSet X,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          simp_rw [Finset.mul_sum]
        _ = ∑ q ∈ Icc 1 Q, ∑ k ∈ dyadicExponentSet X,
            ∑ chi ∈ primitiveCharacters q,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_comm]
        _ = ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
            ∑ chi ∈ primitiveCharacters q,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          rw [Finset.sum_comm]
        _ = _ := by simp_rw [Finset.mul_sum]

theorem typeITwoKernelCoefficient_eq_zero_of_mul_lt
    {u v m : Nat} (huv : u * v < m) :
    typeITwoKernelCoefficient u v m = 0 := by
  unfold typeITwoKernelCoefficient
  apply Finset.sum_eq_zero
  intro factors hfactors
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp hfactors).1
  by_cases hleft : factors.1 <= u
  · by_cases hright : factors.2 <= v
    · have : m <= u * v := by
        rw [← hproduct]
        exact Nat.mul_le_mul hleft hright
      omega
    · simp [hright]
  · simp [hleft]

theorem typeITwoBlockMean_eq_zero_of_upper
    {u v M N X Q : Nat} (huvM : u * v <= M) :
    typeITwoBlockMean u v M N X Q = 0 := by
  have hcoeff : ∀ m, typeITwoBlockLeftCoefficient u v M m = 0 := by
    intro m
    unfold typeITwoBlockLeftCoefficient
    by_cases hs : u < m ∧ M < m ∧ m <= 2 * M
    · rw [if_pos hs, typeITwoKernelCoefficient_eq_zero_of_mul_lt (lt_of_le_of_lt huvM hs.2.1)]
      simp
    · simp [hs]
  unfold typeITwoBlockMean maximalBilinearNorm restrictedBilinearCharacterSum
  simp_rw [hcoeff]
  simp

def activeTypeITwoExponentSet (u v X : Nat) : Finset Nat :=
  (dyadicExponentSet X).filter fun k => u < 2 * 2 ^ k ∧ 2 ^ k < u * v

theorem typeITwoLargeMean_le_sum_activeMajorants
    (u v X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoLargeMean u v X Q <=
      ∑ k ∈ activeTypeITwoExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeITwoLargeMean u v X Q <=
        ∑ k ∈ dyadicExponentSet X,
          typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeITwoLargeMean_le_sum_blockMeans u v X Q hu
    _ = ∑ k ∈ activeTypeITwoExponentSet u v X,
        typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      symm
      unfold activeTypeITwoExponentSet
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hactive : u < 2 * 2 ^ k ∧ 2 ^ k < u * v
      · simp [hactive]
      · have hinactive : 2 * 2 ^ k <= u ∨ u * v <= 2 ^ k := by omega
        rcases hinactive with hlow | hupp
        · have hzero : typeITwoBlockLeftCoefficient u v (2 ^ k) = 0 := by
            funext m
            unfold typeITwoBlockLeftCoefficient
            rw [if_neg (by
              intro hs
              omega)]
            rfl
          unfold typeITwoBlockMean maximalBilinearNorm restrictedBilinearCharacterSum
          simp_rw [hzero]
          simp [hactive]
        · rw [typeITwoBlockMean_eq_zero_of_upper hupp]
          simp [hactive]
    _ <= ∑ k ∈ activeTypeITwoExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
      apply Finset.sum_le_sum
      intro k hk
      exact typeITwoBlockMean_le u v (2 ^ k) (X / 2 ^ k) X Q hX hQ

def typeITwoSourceCore (X u Q : Nat) : Real :=
  2 * (X : Real) + 2 * ((X : Real) * (Q : Real) / Real.sqrt (u : Real)) +
    2 * ((u : Real) * Real.sqrt (X : Real) * (Q : Real)) +
      2 * (Real.sqrt (X : Real) * (Q : Real) ^ 2)

theorem typeITwo_sqrt_core_bound
    {x u m n q : Real}
    (hx : 0 <= x) (hu : 0 < u) (hm : 0 <= m) (hn : 0 <= n) (hq : 0 <= q)
    (hmn : m * n <= x) (hum : u <= 2 * m) (hmu : m <= u ^ 2) :
    Real.sqrt ((2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n) <=
      2 * x + 2 * (x * q / Real.sqrt u) +
        2 * (u * Real.sqrt x * q) + 2 * (Real.sqrt x * q ^ 2) := by
  let A : Real := u * Real.sqrt x * q
  let B : Real := x * q / Real.sqrt u
  let C : Real := Real.sqrt x * q ^ 2
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hA : 0 <= A := by dsimp [A]; positivity
  have hB : 0 <= B := by dsimp [B]; positivity
  have hC : 0 <= C := by dsimp [C]; positivity
  have hA2 : A ^ 2 = u ^ 2 * x * q ^ 2 := by
    dsimp [A]
    rw [mul_pow, mul_pow, Real.sq_sqrt hx]
  have hBmul : B ^ 2 * u = x ^ 2 * q ^ 2 := by
    dsimp [B]
    rw [div_pow, Real.sq_sqrt hu.le]
    field_simp [hu.ne']
  have hC2 : C ^ 2 = x * q ^ 4 := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt hx]
    ring
  have hmnNonneg : 0 <= m * n := mul_nonneg hm hn
  have htermOne : 4 * (m * n) ^ 2 <= 4 * x ^ 2 := by nlinarith
  have hmProduct : m * (m * n) <= u ^ 2 * x :=
    mul_le_mul hmu hmn hmnNonneg (sq_nonneg u)
  have hmProductQ := mul_le_mul_of_nonneg_right hmProduct (sq_nonneg q)
  have htermTwo : 4 * m ^ 2 * n * q ^ 2 <= 4 * A ^ 2 := by
    nlinarith [hA2, hmProductQ]
  have huProduct : u * (m * n ^ 2) <= 2 * (m * n) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hum (mul_nonneg hm (sq_nonneg n))
    nlinarith
  have huProductX : u * (m * n ^ 2) <= 2 * x ^ 2 := by
    have hsquare : (m * n) ^ 2 <= x ^ 2 :=
      (sq_le_sq₀ hmnNonneg hx).2 hmn
    nlinarith [huProduct, hsquare]
  have huProductQ := mul_le_mul_of_nonneg_right huProductX (sq_nonneg q)
  have htermThree : 2 * m * n ^ 2 * q ^ 2 <= 4 * B ^ 2 := by
    have hscaled : (2 * m * n ^ 2 * q ^ 2) * u <= (4 * B ^ 2) * u := by
      nlinarith [huProductQ, hBmul]
    exact (mul_le_mul_iff_of_pos_right hu).mp (by simpa [mul_assoc] using hscaled)
  have htermFour : 2 * m * n * q ^ 4 <= 2 * C ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hmn (by positivity : 0 <= q ^ 4), hC2]
  have hradicand :
      (2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n <=
        (2 * x + 2 * B + 2 * A + 2 * C) ^ 2 := by
    nlinarith [htermOne, htermTwo, htermThree, htermFour,
      sq_nonneg (2 * x + 2 * B + 2 * A + 2 * C)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simpa [A, B, C] using hradicand

theorem active_typeITwoBlockMajorant_le
    (M X u Q : Nat) (hX : 2 <= X) (hu : 1 <= u)
    (hMX : M <= X) (hactive : u < 2 * M ∧ M < u * u) :
    typeIIBlockMajorant M (X / M) X Q <=
      2880 * Real.log (X : Real) ^ 2 * typeITwoSourceCore X u Q := by
  have hMNnat : M * (X / M) <= X := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self X M
  have hMN : (M : Real) * ((X / M : Nat) : Real) <= (X : Real) := by
    exact_mod_cast hMNnat
  have hcore := typeITwo_sqrt_core_bound
    (show 0 <= (X : Real) by positivity)
    (show 0 < (u : Real) by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hu))
    (show 0 <= (M : Real) by positivity)
    (show 0 <= ((X / M : Nat) : Real) by positivity)
    (show 0 <= (Q : Real) by positivity) hMN
    (by exact_mod_cast hactive.1.le)
    (by
      have hNat : M <= u ^ 2 := by simpa [pow_two] using hactive.2.le
      exact_mod_cast hNat)
  have hcore' :
      Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        ((2 * M : Nat) : Real)) *
          ((((X / M : Nat) : Real) + (Q : Real) ^ 2) * ((X / M : Nat) : Real))) <=
        typeITwoSourceCore X u Q := by
    simpa [typeITwoSourceCore, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcore
  have hcutoff : 16 + 4 * Real.log ((X : Real) + 1) <=
      40 * Real.log (X : Real) := by
    simpa using cutoffFactor_le_log_product X 1 1 hX (by norm_num) (by norm_num)
  have hMpos : 0 < M := by omega
  have hlogMX : Real.log (M : Real) <= Real.log (X : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hMpos
    · exact_mod_cast hMX
  have hlogTwoX : Real.log 2 <= Real.log (X : Real) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hX
  have hlogDouble : Real.log ((2 * M : Nat) : Real) <=
      2 * Real.log (X : Real) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : Ne (2 : Real) 0)
      (by exact_mod_cast hMpos.ne' : Ne (M : Real) 0)]
    linarith
  have hsource : 0 <= typeITwoSourceCore X u Q := by
    unfold typeITwoSourceCore
    positivity
  rw [typeIIBlockMajorant_eq_core]
  calc
    _ <= 36 * (40 * Real.log (X : Real)) *
        (2 * Real.log (X : Real)) * typeITwoSourceCore X u Q := by
      gcongr
    _ = 2880 * Real.log (X : Real) ^ 2 * typeITwoSourceCore X u Q := by ring

theorem typeITwoLargeMean_le_sourceScale
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoLargeMean u u X Q <=
      11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q := by
  have hbase := typeITwoLargeMean_le_sum_activeMajorants u u X Q hu hX hQ
  let C : Real := 2880 * Real.log (X : Real) ^ 2 * typeITwoSourceCore X u Q
  have hC : 0 <= C := by
    dsimp [C]
    unfold typeITwoSourceCore
    positivity
  calc
    typeITwoLargeMean u u X Q <=
        ∑ k ∈ activeTypeITwoExponentSet u u X,
          typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := hbase
    _ <= ∑ k ∈ activeTypeITwoExponentSet u u X, C := by
      apply Finset.sum_le_sum
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hkLog : k <= Nat.log 2 X := by
        have hkRange := Finset.mem_range.mp hkData.1
        simp only [dyadicExponentSet] at hkData
        omega
      have hpowX : 2 ^ k <= X := by
        calc
          2 ^ k <= 2 ^ Nat.log 2 X := Nat.pow_le_pow_right (by omega) hkLog
          _ <= X := Nat.pow_log_le_self 2 (by omega)
      exact active_typeITwoBlockMajorant_le (2 ^ k) X u Q hX hu hpowX hkData.2
    _ = ((activeTypeITwoExponentSet u u X).card : Real) * C := by simp
    _ <= ((dyadicExponentSet X).card : Real) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ <= (4 * Real.log (X : Real)) * C := by
      exact mul_le_mul_of_nonneg_right (dyadicExponentSet_card_le_log X hX) hC
    _ = 11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q := by
      dsimp [C]
      ring

end BombieriVinogradov.VaughanMeanValue
