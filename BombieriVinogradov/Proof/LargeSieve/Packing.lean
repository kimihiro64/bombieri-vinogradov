import BombieriVinogradov.Proof.LargeSieve.Farey
import BombieriVinogradov.Proof.LargeSieve.Fejer
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Packing bounds for separated points

The inverse-square Fejer estimate becomes useful only after separated points
are placed in disjoint intervals of the separation length.  This module keeps
that combinatorial packing step independent of the Fourier identities.
-/

set_option autoImplicit false

noncomputable section

open Finset Real
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- The index of the half-open interval of width `delta` containing `x`. -/
def packingBin (delta x : Real) : Nat := Nat.floor (x / delta)

/-- Two nonnegative points in the same positive-width bin are less than one width apart. -/
theorem abs_sub_lt_of_packingBin_eq {delta x y : Real} (hdelta : 0 < delta)
    (hx : 0 <= x) (hy : 0 <= y)
    (hbin : packingBin delta x = packingBin delta y) :
    |x - y| < delta := by
  have hxq0 : 0 <= x / delta := div_nonneg hx hdelta.le
  have hyq0 : 0 <= y / delta := div_nonneg hy hdelta.le
  have hxlo : ((packingBin delta x : Nat) : Real) <= x / delta :=
    Nat.floor_le hxq0
  have hxhi : x / delta < (packingBin delta x : Nat) + 1 :=
    Nat.lt_floor_add_one _
  have hylo : ((packingBin delta y : Nat) : Real) <= y / delta :=
    Nat.floor_le hyq0
  have hyhi : y / delta < (packingBin delta y : Nat) + 1 :=
    Nat.lt_floor_add_one _
  have hxyq : x / delta - y / delta < 1 := by
    rw [hbin] at hxhi
    linarith
  have hyxq : y / delta - x / delta < 1 := by
    rw [hbin] at hxlo
    linarith
  have hxy : x - y < delta := by
    rw [← sub_div] at hxyq
    exact (div_lt_one hdelta).mp hxyq
  have hyx : y - x < delta := by
    rw [← sub_div] at hyxq
    exact (div_lt_one hdelta).mp hyxq
  rw [abs_lt]
  exact And.intro (by linarith) hxy

/-- A `delta`-separated family of nonnegative points has injective bin indices. -/
theorem packingBin_injective {ι : Type*} {delta : Real} (hdelta : 0 < delta)
    (x : ι -> Real) (hx : ∀ i, 0 <= x i)
    (hsep : ∀ i j, Ne i j -> delta <= |x i - x j|) :
    Function.Injective (fun i => packingBin delta (x i)) := by
  intro i j hbin
  by_contra hij
  have hlt := abs_sub_lt_of_packingBin_eq hdelta (hx i) (hx j) hbin
  exact (not_lt_of_ge (hsep i j hij)) hlt

/-- The two pointwise Fejer bounds expressed at the `k`-th separation bin. -/
def fejerRankMajorant (N : Nat) (delta : Real) (k : Nat) : Real :=
  if k = 0 then 0
  else min (2 * (N : Real))
    (1 / (2 * (N : Real) * ((k : Real) * delta) ^ 2))

theorem fejerRankMajorant_nonneg {N : Nat} (hN : 0 < N)
    {delta : Real} (hdelta : 0 < delta) (k : Nat) :
    0 <= fejerRankMajorant N delta k := by
  rw [fejerRankMajorant]
  split_ifs
  · exact le_rfl
  · rw [le_min_iff]
    exact And.intro (by positivity) (by positivity)

theorem fejerRankMajorant_le_diagonal (N : Nat) (delta : Real) (k : Nat) :
    fejerRankMajorant N delta k <= 2 * (N : Real) := by
  rw [fejerRankMajorant]
  split_ifs
  · positivity
  · exact min_le_left _ _

theorem fejerRankMajorant_le_inv {N k : Nat} (hN : 0 < N) (hk : Ne k 0)
    {delta : Real} (hdelta : 0 < delta) :
    fejerRankMajorant N delta k <=
      (1 / (2 * (N : Real) * delta ^ 2)) * (((k : Real) ^ 2)⁻¹) := by
  rw [fejerRankMajorant, if_neg hk]
  calc
    min (2 * (N : Real))
        (1 / (2 * (N : Real) * ((k : Real) * delta) ^ 2)) <=
      1 / (2 * (N : Real) * ((k : Real) * delta) ^ 2) := min_le_right _ _
    _ = (1 / (2 * (N : Real) * delta ^ 2)) * (((k : Real) ^ 2)⁻¹) := by
      field_simp [Nat.ne_of_gt hN, hk, ne_of_gt hdelta]

/-- The separated inverse-square bin majorants have a uniform finite sum. -/
theorem sum_fejerRankMajorant_le {N : Nat} (hN : 0 < N)
    {delta : Real} (hdelta : 0 < delta) (K : Nat) :
    ∑ k ∈ range K, fejerRankMajorant N delta k <=
      4 * (N : Real) + 5 / (2 * delta) := by
  let a : Real := 1 / ((N : Real) * delta)
  let A : Nat := Nat.ceil a
  have ha0 : 0 < a := by simp [a]; positivity
  have hAone : 1 <= A := Nat.one_le_ceil_iff.mpr ha0
  have hAne : Ne A 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hAone)
  have hApos : (0 : Real) < A := by exact_mod_cast hAone
  have hAle : a <= (A : Real) := Nat.le_ceil a
  have hAlt : (A : Real) < a + 1 := Nat.ceil_lt_add_one ha0.le
  let head : Finset Nat := (range K).filter fun k => k <= A
  let tail : Finset Nat := (range K).filter fun k => ¬k <= A
  have hhead_subset : head ⊆ range (A + 1) := by
    intro k hk
    simp only [head, mem_filter] at hk
    exact mem_range.mpr (Nat.lt_succ_iff.mpr hk.2)
  have hhead_card : (head.card : Real) <= A + 1 := by
    have hcardNat : head.card <= A + 1 := by
      simpa using Finset.card_le_card hhead_subset
    exact_mod_cast hcardNat
  have hhead : ∑ k ∈ head, fejerRankMajorant N delta k <=
      2 * (N : Real) * (A + 1) := by
    calc
      ∑ k ∈ head, fejerRankMajorant N delta k <=
          ∑ k ∈ head, 2 * (N : Real) :=
        Finset.sum_le_sum fun k hk => fejerRankMajorant_le_diagonal N delta k
      _ = head.card * (2 * (N : Real)) := by simp
      _ <= 2 * (N : Real) * (A + 1) := by
        nlinarith
  have hhead_final : ∑ k ∈ head, fejerRankMajorant N delta k <=
      4 * (N : Real) + 2 / delta := by
    apply hhead.trans
    have hAone' : (A : Real) + 1 <= a + 2 := by linarith
    calc
      2 * (N : Real) * ((A : Real) + 1) <=
          2 * (N : Real) * (a + 2) := by gcongr
      _ = 4 * (N : Real) + 2 / delta := by
        dsimp [a]
        field_simp [Nat.ne_of_gt hN, ne_of_gt hdelta]
        ring
  have htail_subset : tail ⊆ Ioc A (max A K) := by
    intro k hk
    simp only [tail, mem_filter, mem_range] at hk
    exact mem_Ioc.mpr ⟨Nat.lt_of_not_ge hk.2, (Nat.le_of_lt hk.1).trans (le_max_right _ _)⟩
  have htail_inv : ∑ k ∈ tail, (((k : Real) ^ 2)⁻¹) <= ((A : Real)⁻¹) := by
    calc
      ∑ k ∈ tail, (((k : Real) ^ 2)⁻¹) <=
          ∑ k ∈ Ioc A (max A K), (((k : Real) ^ 2)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg htail_subset (by
          intro k hk hnot
          positivity)
      _ <= (A : Real)⁻¹ - (((max A K : Nat) : Real)⁻¹) :=
        sum_Ioc_inv_sq_le_sub hAne (le_max_left _ _)
      _ <= (A : Real)⁻¹ := by
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have htail : ∑ k ∈ tail, fejerRankMajorant N delta k <=
      (1 / (2 * (N : Real) * delta ^ 2)) * ((A : Real)⁻¹) := by
    calc
      ∑ k ∈ tail, fejerRankMajorant N delta k <=
          ∑ k ∈ tail,
            (1 / (2 * (N : Real) * delta ^ 2)) * (((k : Real) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkA : A < k := by
          simp only [tail, mem_filter] at hk
          exact Nat.lt_of_not_ge hk.2
        have hk0 : Ne k 0 := by omega
        exact fejerRankMajorant_le_inv hN hk0 hdelta
      _ = (1 / (2 * (N : Real) * delta ^ 2)) *
          ∑ k ∈ tail, (((k : Real) ^ 2)⁻¹) := by rw [Finset.mul_sum]
      _ <= (1 / (2 * (N : Real) * delta ^ 2)) * ((A : Real)⁻¹) := by
        gcongr
  have hAinv : ((A : Real)⁻¹) <= (N : Real) * delta := by
    apply (inv_le_iff_one_le_mul₀ hApos).2
    have hmul := mul_le_mul_of_nonneg_left hAle
      (mul_nonneg (Nat.cast_nonneg N) hdelta.le)
    have hcancel : (N : Real) * delta * a = 1 := by
      dsimp [a]
      field_simp [Nat.ne_of_gt hN, ne_of_gt hdelta]
    nlinarith
  have htail_final : ∑ k ∈ tail, fejerRankMajorant N delta k <=
      1 / (2 * delta) := by
    apply htail.trans
    calc
      (1 / (2 * (N : Real) * delta ^ 2)) * ((A : Real)⁻¹) <=
          (1 / (2 * (N : Real) * delta ^ 2)) * ((N : Real) * delta) := by
        gcongr
      _ = 1 / (2 * delta) := by
        field_simp [Nat.ne_of_gt hN, ne_of_gt hdelta]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (range K) (fun k => k <= A) (fejerRankMajorant N delta)
  change (∑ k ∈ head, fejerRankMajorant N delta k) +
      (∑ k ∈ tail, fejerRankMajorant N delta k) =
        ∑ k ∈ range K, fejerRankMajorant N delta k at hsplit
  calc
    ∑ k ∈ range K, fejerRankMajorant N delta k =
        (∑ k ∈ head, fejerRankMajorant N delta k) +
          (∑ k ∈ tail, fejerRankMajorant N delta k) := hsplit.symm
    _ <= (4 * (N : Real) + 2 / delta) + 1 / (2 * delta) :=
      add_le_add hhead_final htail_final
    _ = 4 * (N : Real) + 5 / (2 * delta) := by ring

/-- Reindex a nonnegative majorant through an injective finite natural-valued rank. -/
theorem sum_le_sum_range_of_injective {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι -> Nat) (K : Nat)
    (he : ∀ i ∈ s, e i < K) (hinj : Set.InjOn e (s : Set ι))
    (g : Nat -> Real) (hg : ∀ k, 0 <= g k)
    (w : ι -> Real) (hw : ∀ i ∈ s, w i <= g (e i)) :
    ∑ i ∈ s, w i <= ∑ k ∈ range K, g k := by
  have hsubset : s.image e ⊆ range K := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    exact mem_range.mpr (he i hi)
  calc
    ∑ i ∈ s, w i <= ∑ i ∈ s, g (e i) :=
      Finset.sum_le_sum fun i hi => hw i hi
    _ = ∑ k ∈ s.image e, g k := (Finset.sum_image hinj).symm
    _ <= ∑ k ∈ range K, g k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro k hk hnot
        exact hg k)

/-- One side of a separated Fejer row is bounded uniformly by packing bins. -/
theorem packedFejerSum {ι : Type*} [DecidableEq ι]
    {N : Nat} (hN : 0 < N) {delta : Real} (hdelta : 0 < delta)
    (s : Finset ι) (d : ι -> Real)
    (hd0 : ∀ i ∈ s, delta <= d i) (hd1 : ∀ i ∈ s, d i < 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, Ne i j -> delta <= |d i - d j|)
    (w : ι -> Real)
    (hw : ∀ i ∈ s, w i <=
      min (2 * (N : Real)) (1 / (2 * (N : Real) * d i ^ 2))) :
    ∑ i ∈ s, w i <= 4 * (N : Real) + 5 / (2 * delta) := by
  let e : ι -> Nat := fun i => packingBin delta (d i)
  let K : Nat := Nat.ceil (1 / delta)
  have hdnonneg : ∀ i ∈ s, 0 <= d i := by
    intro i hi
    exact hdelta.le.trans (hd0 i hi)
  have heinj : Set.InjOn e (s : Set ι) := by
    intro i hi j hj heq
    by_contra hij
    have hlt := abs_sub_lt_of_packingBin_eq hdelta
      (hdnonneg i hi) (hdnonneg j hj) heq
    exact (not_lt_of_ge (hsep i hi j hj hij)) hlt
  have heK : ∀ i ∈ s, e i < K := by
    intro i hi
    apply Nat.floor_lt_ceil_of_lt_of_pos
    · exact (div_lt_div_iff_of_pos_right hdelta).2 (hd1 i hi)
    · positivity
  have hweight : ∀ i ∈ s, w i <= fejerRankMajorant N delta (e i) := by
    intro i hi
    have hquot : ((1 : Nat) : Real) <= d i / delta :=
      (le_div_iff₀ hdelta).2 (by simpa using hd0 i hi)
    have heone : 1 <= e i := Nat.le_floor hquot
    have he0 : Ne (e i) 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le heone)
    have hfloor : ((e i : Nat) : Real) <= d i / delta :=
      Nat.floor_le (div_nonneg (hdnonneg i hi) hdelta.le)
    have helower : (e i : Real) * delta <= d i := by
      have hmul := mul_le_mul_of_nonneg_right hfloor hdelta.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hdelta)] at hmul
    apply (hw i hi).trans
    rw [fejerRankMajorant, if_neg he0]
    apply min_le_min le_rfl
    apply one_div_le_one_div_of_le
    · positivity
    · have hesq : ((e i : Real) * delta) ^ 2 <= d i ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) helower 2
      nlinarith [show (0 : Real) < N by exact_mod_cast hN]
  calc
    ∑ i ∈ s, w i <= ∑ k ∈ range K, fejerRankMajorant N delta k :=
      sum_le_sum_range_of_injective s e K heK heinj
        (fejerRankMajorant N delta)
        (fejerRankMajorant_nonneg hN hdelta) w hweight
    _ <= 4 * (N : Real) + 5 / (2 * delta) :=
      sum_fejerRankMajorant_le hN hdelta K

end BombieriVinogradov.LargeSieve
