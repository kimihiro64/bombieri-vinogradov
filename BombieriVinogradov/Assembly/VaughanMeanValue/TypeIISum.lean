import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIIDyadic
import Mathlib.Tactic

/-!
# Source-scale estimate for Vaughan's Type II contribution

Inactive dyadic blocks vanish exactly. The remaining block square-root
majorants are controlled by the lower and upper cutoff inequalities, and their
logarithmic-size sum yields Vaughan's source-scale Type II estimate.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

def activeDyadicExponentSet (u v X : Nat) : Finset Nat :=
  (dyadicExponentSet X).filter fun k =>
    u < 2 * 2 ^ k ∧ v < X / 2 ^ k

theorem typeIIBlockLeftCoefficient_eq_zero_of_double_le
    {u M : Nat} (hMu : 2 * M <= u) (m : Nat) :
    typeIIBlockLeftCoefficient u M m = 0 := by
  by_cases hsupport : M < m ∧ m <= 2 * M
  · rw [typeIIBlockLeftCoefficient, if_pos hsupport]
    rw [typeIILeftKernelCoefficient_eq_zero_of_le (hsupport.2.trans hMu)]
    rfl
  · simp [typeIIBlockLeftCoefficient, hsupport]

theorem typeIIBlockMean_eq_zero_of_left
    {u v M N X Q : Nat} (hMu : 2 * M <= u) :
    typeIIBlockMean u v M N X Q = 0 := by
  have hleft : typeIIBlockLeftCoefficient u M = 0 := by
    funext m
    exact typeIIBlockLeftCoefficient_eq_zero_of_double_le hMu m
  unfold typeIIBlockMean maximalBilinearNorm restrictedBilinearCharacterSum
  rw [hleft]
  simp

theorem restricted_typeIIBlock_eq_zero_of_right
    {u v M N Y q : Nat} (hNv : N <= v)
    (chi : DirichletCharacter Complex q) :
    restrictedBilinearCharacterSum
      (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v)
      (2 * M) N Y q chi = 0 := by
  unfold restrictedBilinearCharacterSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hnv : n <= v := (Finset.mem_Icc.mp hn).2.trans hNv
  simp [typeIIRightCoefficient, hnv]

theorem typeIIBlockMean_eq_zero_of_right
    {u v M N X Q : Nat} (hNv : N <= v) :
    typeIIBlockMean u v M N X Q = 0 := by
  unfold typeIIBlockMean maximalBilinearNorm
  simp_rw [restricted_typeIIBlock_eq_zero_of_right hNv]
  simp

theorem typeIIBlockMean_eq_zero_of_inactive
    {u v M N X Q : Nat} (hinactive : 2 * M <= u ∨ N <= v) :
    typeIIBlockMean u v M N X Q = 0 := by
  rcases hinactive with hleft | hright
  · exact typeIIBlockMean_eq_zero_of_left hleft
  · exact typeIIBlockMean_eq_zero_of_right hright

theorem typeIIDyadicMean_le_sum_activeBlockMeans
    (u v X Q : Nat) (hu : 1 <= u) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeIIDyadicMean u v X Q <=
        ∑ k ∈ dyadicExponentSet X,
          typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeIIDyadicMean_le_sum_blockMeans u v X Q hu
    _ = ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      symm
      unfold activeDyadicExponentSet
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hactive : u < 2 * 2 ^ k ∧ v < X / 2 ^ k
      · simp [hactive]
      · have hinactive : 2 * 2 ^ k <= u ∨ X / 2 ^ k <= v := by omega
        rw [typeIIBlockMean_eq_zero_of_inactive hinactive]
        simp [hactive]

theorem typeIIDyadicMean_le_sum_activeMajorants
    (u v X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeIIDyadicMean u v X Q <=
        ∑ k ∈ activeDyadicExponentSet u v X,
          typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeIIDyadicMean_le_sum_activeBlockMeans u v X Q hu
    _ <= ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [typeIIBlockMajorant] using
        typeIIBlockMean_le u v (2 ^ k) (X / 2 ^ k) X Q hX hQ

theorem typeII_sqrt_core_bound
    {x u m n q : Real}
    (hx : 0 <= x) (hu : 0 < u) (hm : 0 <= m) (hn : 0 <= n) (hq : 0 <= q)
    (hmn : m * n <= x) (hum : u <= 2 * m) (hun : u <= n) :
    Real.sqrt ((2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n) <=
      2 * x + 3 * (x * q / Real.sqrt u) +
        2 * (Real.sqrt x * q ^ 2) := by
  let B : Real := x * q / Real.sqrt u
  let C : Real := Real.sqrt x * q ^ 2
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hB : 0 <= B := by dsimp [B]; positivity
  have hC : 0 <= C := by dsimp [C]; positivity
  have hBmul : B ^ 2 * u = x ^ 2 * q ^ 2 := by
    dsimp [B]
    rw [div_pow, Real.sq_sqrt hu.le]
    field_simp [hu.ne']
  have hCsq : C ^ 2 = x * q ^ 4 := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt hx]
    ring
  have hmu : m * u <= x := by
    exact (mul_le_mul_of_nonneg_left hun hm).trans hmn
  have hunTwo : u * n <= 2 * x := by
    calc
      u * n <= (2 * m) * n := mul_le_mul_of_nonneg_right hum hn
      _ = 2 * (m * n) := by ring
      _ <= 2 * x := by linarith
  have hmnNonneg : 0 <= m * n := mul_nonneg hm hn
  have htermOne : (m * n) ^ 2 <= x ^ 2 := by nlinarith
  have hprodTwo : (m * n) * (m * u) <= x * x :=
    mul_le_mul hmn hmu (mul_nonneg hm hu.le) hx
  have hprodTwoQ := mul_le_mul_of_nonneg_right hprodTwo (sq_nonneg q)
  have htermTwo : m ^ 2 * n * q ^ 2 <= B ^ 2 := by
    have hscaled : (m ^ 2 * n * q ^ 2) * u <= (B ^ 2) * u := by
      nlinarith [hprodTwoQ, hBmul]
    exact (mul_le_mul_iff_of_pos_right hu).mp (by simpa [mul_assoc] using hscaled)
  have hprodThree : (m * n) * (u * n) <= x * (2 * x) :=
    mul_le_mul hmn hunTwo (mul_nonneg hu.le hn) hx
  have hprodThreeQ := mul_le_mul_of_nonneg_right hprodThree (sq_nonneg q)
  have htermThree : m * n ^ 2 * q ^ 2 <= 2 * B ^ 2 := by
    have hscaled : (m * n ^ 2 * q ^ 2) * u <= (2 * B ^ 2) * u := by
      nlinarith [hprodThreeQ, hBmul]
    exact (mul_le_mul_iff_of_pos_right hu).mp (by simpa [mul_assoc] using hscaled)
  have htermFour : m * n * q ^ 4 <= C ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hmn (by positivity : 0 <= q ^ 4), hCsq]
  have hradicand :
      (2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n <=
        (2 * x + 3 * B + 2 * C) ^ 2 := by
    nlinarith [htermOne, htermTwo, htermThree, htermFour,
      sq_nonneg (2 * x + 3 * B + 2 * C)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simpa [B, C] using hradicand

theorem typeIIBlockMajorant_eq_core (M N X Q : Nat) :
    typeIIBlockMajorant M N X Q =
      36 * (16 + 4 * Real.log ((X : Real) + 1)) *
        Real.log ((2 * M : Nat) : Real) *
          Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
            ((2 * M : Nat) : Real)) *
              (((N : Real) + (Q : Real) ^ 2) * (N : Real))) := by
  let L : Real := Real.log ((2 * M : Nat) : Real)
  let U : Real := ((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
    (((2 * M : Nat) : Real) * L ^ 2))
  let V : Real := (((N : Real) + (Q : Real) ^ 2) * (N : Real))
  have hU : 0 <= U := by dsimp [U]; positivity
  have hL : 0 <= L := by
    dsimp [L]
    exact Real.log_natCast_nonneg (2 * M)
  unfold typeIIBlockMajorant
  rw [show 36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
      (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2) =
        36 * U by dsimp [U, L]; ring]
  rw [show 36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real) =
      36 * V by dsimp [V]; ring]
  rw [sqrt_thirtySix_mul_product U V hU]
  have hfactor : U * V = L ^ 2 *
      (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        ((2 * M : Nat) : Real)) *
          (((N : Real) + (Q : Real) ^ 2) * (N : Real))) := by
    dsimp [U, V]
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq_eq_abs, abs_of_nonneg hL]
  dsimp [L]
  ring

def typeIISourceCore (X u Q : Nat) : Real :=
  2 * (X : Real) + 3 * ((X : Real) * (Q : Real) / Real.sqrt (u : Real)) +
    2 * (Real.sqrt (X : Real) * (Q : Real) ^ 2)

theorem active_typeIIBlockMajorant_le
    (M X u Q : Nat) (hX : 2 <= X) (hu : 1 <= u)
    (hMX : M <= X) (hactive : u < 2 * M ∧ u < X / M) :
    typeIIBlockMajorant M (X / M) X Q <=
      2880 * Real.log (X : Real) ^ 2 * typeIISourceCore X u Q := by
  have hXnonneg : 0 <= (X : Real) := by positivity
  have hupos : 0 < (u : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hu)
  have hMnonneg : 0 <= (M : Real) := by positivity
  have hNnonneg : 0 <= ((X / M : Nat) : Real) := by positivity
  have hQnonneg : 0 <= (Q : Real) := by positivity
  have hMNnat : M * (X / M) <= X := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self X M
  have hMN : (M : Real) * ((X / M : Nat) : Real) <= (X : Real) := by
    exact_mod_cast hMNnat
  have huM : (u : Real) <= 2 * (M : Real) := by
    exact_mod_cast hactive.1.le
  have huN : (u : Real) <= ((X / M : Nat) : Real) := by
    exact_mod_cast hactive.2.le
  have hcore := typeII_sqrt_core_bound hXnonneg hupos hMnonneg hNnonneg hQnonneg
    hMN huM huN
  have hcore' :
      Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        ((2 * M : Nat) : Real)) *
          ((((X / M : Nat) : Real) + (Q : Real) ^ 2) * ((X / M : Nat) : Real))) <=
        2 * (X : Real) + 3 * ((X : Real) * (Q : Real) / Real.sqrt (u : Real)) +
          2 * (Real.sqrt (X : Real) * (Q : Real) ^ 2) := by
    simpa [typeIISourceCore, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcore
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
  have hlogX : 0 <= Real.log (X : Real) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hX))
  have hsource : 0 <= typeIISourceCore X u Q := by
    unfold typeIISourceCore
    positivity
  rw [typeIIBlockMajorant_eq_core]
  calc
    36 * (16 + 4 * Real.log ((X : Real) + 1)) *
          Real.log ((2 * M : Nat) : Real) *
            Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
              ((2 * M : Nat) : Real)) *
                ((((X / M : Nat) : Real) + (Q : Real) ^ 2) *
                  ((X / M : Nat) : Real))) <=
        36 * (40 * Real.log (X : Real)) *
          (2 * Real.log (X : Real)) * typeIISourceCore X u Q := by
      unfold typeIISourceCore
      gcongr
    _ = 2880 * Real.log (X : Real) ^ 2 * typeIISourceCore X u Q := by ring

theorem dyadicExponentSet_card_le_log (X : Nat) (hX : 2 <= X) :
    ((dyadicExponentSet X).card : Real) <= 4 * Real.log (X : Real) := by
  have hXne : Ne X 0 := by omega
  have hpowNat : 2 ^ Nat.log 2 X <= X := Nat.pow_log_le_self 2 hXne
  have hpow : ((2 : Real) ^ Nat.log 2 X) <= (X : Real) := by
    exact_mod_cast hpowNat
  have hpowPos : 0 < ((2 : Real) ^ Nat.log 2 X) := by positivity
  have hlogPow : Real.log ((2 : Real) ^ Nat.log 2 X) <= Real.log (X : Real) :=
    Real.log_le_log hpowPos hpow
  rw [Real.log_pow] at hlogPow
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogTwoX : Real.log 2 <= Real.log (X : Real) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hX
  have hcard : (dyadicExponentSet X).card = Nat.log 2 X + 1 := by
    simp [dyadicExponentSet]
  rw [hcard]
  push_cast
  nlinarith

theorem typeIIDyadicMean_le_sourceScale
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIDyadicMean u u X Q <=
      11520 * Real.log (X : Real) ^ 3 * typeIISourceCore X u Q := by
  have hbase := typeIIDyadicMean_le_sum_activeMajorants u u X Q hu hX hQ
  have hlogX : 0 <= Real.log (X : Real) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hX))
  have hsource : 0 <= typeIISourceCore X u Q := by
    unfold typeIISourceCore
    positivity
  let C : Real := 2880 * Real.log (X : Real) ^ 2 * typeIISourceCore X u Q
  have hC : 0 <= C := by dsimp [C]; positivity
  calc
    typeIIDyadicMean u u X Q <=
        ∑ k ∈ activeDyadicExponentSet u u X,
          typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := hbase
    _ <= ∑ k ∈ activeDyadicExponentSet u u X, C := by
      apply Finset.sum_le_sum
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hkLog : k <= Nat.log 2 X := by
        have := Finset.mem_range.mp hkData.1
        simp only [dyadicExponentSet] at hkData
        omega
      have hpowX : 2 ^ k <= X := by
        calc
          2 ^ k <= 2 ^ Nat.log 2 X := Nat.pow_le_pow_right (by omega) hkLog
          _ <= X := Nat.pow_log_le_self 2 (by omega)
      exact active_typeIIBlockMajorant_le (2 ^ k) X u Q hX hu hpowX hkData.2
    _ = ((activeDyadicExponentSet u u X).card : Real) * C := by simp
    _ <= ((dyadicExponentSet X).card : Real) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ <= (4 * Real.log (X : Real)) * C := by
      exact mul_le_mul_of_nonneg_right (dyadicExponentSet_card_le_log X hX) hC
    _ = 11520 * Real.log (X : Real) ^ 3 * typeIISourceCore X u Q := by
      dsimp [C]
      ring

end BombieriVinogradov.VaughanMeanValue
