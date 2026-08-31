import BombieriVinogradov.Proof.LargeSieve.Packing

/-!
# Fejer row bounds for Farey points

This module connects the generic packing theorem to the reduced rational
points used in the additive large sieve.
-/

set_option autoImplicit false

noncomputable section

open Finset Real
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- A linearly parameterized portion of one Farey row satisfies the packing bound. -/
theorem fareyFejerSubsum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) (s : Finset (FareyIndex Q)) (d : FareyIndex Q -> Real)
    (hdist : ∀ y ∈ s, ratCircleDistance (fareyValue x) (fareyValue y) = d y)
    (hdlt : ∀ y ∈ s, d y < 1)
    (hdiff : ∀ y ∈ s, ∀ z ∈ s,
      |d y - d z| = |(fareyValue y : Real) - (fareyValue z : Real)|)
    (hne : ∀ y ∈ s, Ne x y) :
    ∑ y ∈ s,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  let delta : Real := (1 : Real) / (Q : Real) ^ 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  apply packedFejerSum hN hdelta s d
  · intro y hy
    rw [← hdist y hy]
    exact fareyValue_circle_separation hQ (hne y hy)
  · exact hdlt
  · intro y hy z hz hyz
    calc
      delta <= ratCircleDistance (fareyValue y) (fareyValue z) :=
        fareyValue_circle_separation hQ hyz
      _ <= |(fareyValue y : Real) - (fareyValue z : Real)| := by
        exact min_le_left _ _
      _ = |d y - d z| := (hdiff y hy z hz).symm
  · intro y hy
    rw [le_min_iff]
    constructor
    · exact fejerKernel_le N _
    · have hvalue : Ne (fareyValue x) (fareyValue y) := by
        intro hxy
        exact hne y hy (fareyValue_injective Q hxy)
      have hinv := fejerKernel_rat_sub_le hN
          (fareyValue_nonneg x) (fareyValue_lt_one x)
          (fareyValue_nonneg y) (fareyValue_lt_one y) hvalue
      rwa [hdist y hy] at hinv

/-- The explicit finite enumeration of all reduced Farey indices. -/
def fareyIndices (Q : Nat) : Finset (FareyIndex Q) :=
  (Icc 1 Q).attach.sigma fun q => by
    letI : Fintype (ZMod q.1)ˣ := Fintype.ofFinite _
    exact Finset.univ

@[simp]
theorem mem_fareyIndices {Q : Nat} (x : FareyIndex Q) : x ∈ fareyIndices Q := by
  rcases x with ⟨q, a⟩
  simp [fareyIndices]

def fareyRightNear {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue x : Real) < (fareyValue y : Real) ∧
      (fareyValue y : Real) - (fareyValue x : Real) <= 1 / 2

def fareyRightFar {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue x : Real) < (fareyValue y : Real) ∧
      1 / 2 < (fareyValue y : Real) - (fareyValue x : Real)

def fareyLeftNear {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue y : Real) < (fareyValue x : Real) ∧
      (fareyValue x : Real) - (fareyValue y : Real) <= 1 / 2

def fareyLeftFar {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue y : Real) < (fareyValue x : Real) ∧
      1 / 2 < (fareyValue x : Real) - (fareyValue y : Real)

theorem fareyRightNear_disjoint_rightFar {Q : Nat} (x : FareyIndex Q) :
    Disjoint (fareyRightNear x) (fareyRightFar x) := by
  rw [Finset.disjoint_left]
  intro y hyNear hyFar
  simp only [fareyRightNear, fareyRightFar, mem_filter] at hyNear hyFar
  linarith [hyNear.2.2, hyFar.2.2]

theorem fareyLeftNear_disjoint_leftFar {Q : Nat} (x : FareyIndex Q) :
    Disjoint (fareyLeftNear x) (fareyLeftFar x) := by
  rw [Finset.disjoint_left]
  intro y hyNear hyFar
  simp only [fareyLeftNear, fareyLeftFar, mem_filter] at hyNear hyFar
  linarith [hyNear.2.2, hyFar.2.2]

theorem fareyRight_disjoint_left {Q : Nat} (x : FareyIndex Q) :
    Disjoint (fareyRightNear x ∪ fareyRightFar x)
      (fareyLeftNear x ∪ fareyLeftFar x) := by
  rw [Finset.disjoint_left]
  intro y hyRight hyLeft
  simp only [mem_union] at hyRight hyLeft
  rcases hyRight with hyNear | hyFar
  · rcases hyLeft with hzNear | hzFar
    · simp only [fareyRightNear, fareyLeftNear, mem_filter] at hyNear hzNear
      linarith [hyNear.2.1, hzNear.2.1]
    · simp only [fareyRightNear, fareyLeftFar, mem_filter] at hyNear hzFar
      linarith [hyNear.2.1, hzFar.2.1]
  · rcases hyLeft with hzNear | hzFar
    · simp only [fareyRightFar, fareyLeftNear, mem_filter] at hyFar hzNear
      linarith [hyFar.2.1, hzNear.2.1]
    · simp only [fareyRightFar, fareyLeftFar, mem_filter] at hyFar hzFar
      linarith [hyFar.2.1, hzFar.2.1]

theorem fareyOffdiag_partition {Q : Nat} (x : FareyIndex Q) :
    (fareyIndices Q).erase x =
      (fareyRightNear x ∪ fareyRightFar x) ∪
        (fareyLeftNear x ∪ fareyLeftFar x) := by
  ext y
  simp only [mem_erase, mem_fareyIndices, and_true, mem_union,
    fareyRightNear, fareyRightFar, fareyLeftNear, fareyLeftFar, mem_filter]
  constructor
  · intro hy
    have hvalue : Ne (fareyValue y : Real) (fareyValue x : Real) := by
      intro hxy
      have hrat : fareyValue y = fareyValue x := by exact_mod_cast hxy
      exact hy (fareyValue_injective Q hrat)
    rcases lt_or_gt_of_ne hvalue with hyx | hxy
    · by_cases hhalf : (fareyValue x : Real) - (fareyValue y : Real) <= 1 / 2
      · exact Or.inr (Or.inl ⟨trivial, hyx, hhalf⟩)
      · exact Or.inr (Or.inr ⟨trivial, hyx, lt_of_not_ge hhalf⟩)
    · by_cases hhalf : (fareyValue y : Real) - (fareyValue x : Real) <= 1 / 2
      · exact Or.inl (Or.inl ⟨trivial, hxy, hhalf⟩)
      · exact Or.inl (Or.inr ⟨trivial, hxy, lt_of_not_ge hhalf⟩)
  · intro hy
    rcases hy with (⟨_, hxy, _⟩ | ⟨_, hxy, _⟩) |
      (⟨_, hyx, _⟩ | ⟨_, hyx, _⟩)
    · exact fun heq => by subst y; exact lt_irrefl _ hxy
    · exact fun heq => by subst y; exact lt_irrefl _ hxy
    · exact fun heq => by subst y; exact lt_irrefl _ hyx
    · exact fun heq => by subst y; exact lt_irrefl _ hyx

theorem fareyRightNear_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyRightNear x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyRightNear x)
    (fun y => (fareyValue y : Real) - (fareyValue x : Real))
  · intro y hy
    simp only [fareyRightNear, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue y : Real) - (fareyValue x : Real) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy.2.1)), neg_sub]
    rw [habs, min_eq_left]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyRightNear, mem_filter] at hy
    have hx0 : (0 : Real) <= fareyValue x := by
      exact_mod_cast fareyValue_nonneg x
    have hy1 : (fareyValue y : Real) < 1 := by
      exact_mod_cast fareyValue_lt_one y
    linarith
  · intro y hy z hz
    congr 1
    ring
  · intro y hy hxy
    subst y
    simp only [fareyRightNear, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)

theorem fareyRightFar_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyRightFar x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyRightFar x)
    (fun y => 1 - ((fareyValue y : Real) - (fareyValue x : Real)))
  · intro y hy
    simp only [fareyRightFar, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue y : Real) - (fareyValue x : Real) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy.2.1)), neg_sub]
    rw [habs, min_eq_right]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyRightFar, mem_filter] at hy
    linarith [hy.2.1]
  · intro y hy z hz
    rw [show
      (1 - ((fareyValue y : Real) - (fareyValue x : Real))) -
          (1 - ((fareyValue z : Real) - (fareyValue x : Real))) =
        -((fareyValue y : Real) - (fareyValue z : Real)) by ring, abs_neg]
  · intro y hy hxy
    subst y
    simp only [fareyRightFar, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)

theorem fareyLeftNear_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyLeftNear x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyLeftNear x)
    (fun y => (fareyValue x : Real) - (fareyValue y : Real))
  · intro y hy
    simp only [fareyLeftNear, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue x : Real) - (fareyValue y : Real) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hy.2.1))]
    rw [habs, min_eq_left]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyLeftNear, mem_filter] at hy
    have hx1 : (fareyValue x : Real) < 1 := by
      exact_mod_cast fareyValue_lt_one x
    have hy0 : (0 : Real) <= fareyValue y := by
      exact_mod_cast fareyValue_nonneg y
    linarith
  · intro y hy z hz
    rw [show
      ((fareyValue x : Real) - (fareyValue y : Real)) -
          ((fareyValue x : Real) - (fareyValue z : Real)) =
        -((fareyValue y : Real) - (fareyValue z : Real)) by ring, abs_neg]
  · intro y hy hxy
    subst y
    simp only [fareyLeftNear, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)

theorem fareyLeftFar_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyLeftFar x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyLeftFar x)
    (fun y => 1 - ((fareyValue x : Real) - (fareyValue y : Real)))
  · intro y hy
    simp only [fareyLeftFar, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue x : Real) - (fareyValue y : Real) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hy.2.1))]
    rw [habs, min_eq_right]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyLeftFar, mem_filter] at hy
    linarith [hy.2.1]
  · intro y hy z hz
    congr 1
    ring
  · intro y hy hxy
    subst y
    simp only [fareyLeftFar, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)

/-- Every Farey Fejer row has the source-order bound `O(N + Q^2)`. -/
theorem fareyFejerRowSum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyIndices Q,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      18 * ((N : Real) + (Q : Real) ^ 2) := by
  let f : FareyIndex Q -> Real := fun y =>
    fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real))
  let B : Real := 4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2))
  have hpartition : ∑ y ∈ (fareyIndices Q).erase x, f y =
      (∑ y ∈ fareyRightNear x, f y) + (∑ y ∈ fareyRightFar x, f y) +
        ((∑ y ∈ fareyLeftNear x, f y) + (∑ y ∈ fareyLeftFar x, f y)) := by
    rw [fareyOffdiag_partition]
    rw [Finset.sum_union (fareyRight_disjoint_left x)]
    rw [Finset.sum_union (fareyRightNear_disjoint_rightFar x)]
    rw [Finset.sum_union (fareyLeftNear_disjoint_leftFar x)]
  have hrightNear : ∑ y ∈ fareyRightNear x, f y <= B := by
    exact fareyRightNear_sum hQ hN x
  have hrightFar : ∑ y ∈ fareyRightFar x, f y <= B := by
    exact fareyRightFar_sum hQ hN x
  have hleftNear : ∑ y ∈ fareyLeftNear x, f y <= B := by
    exact fareyLeftNear_sum hQ hN x
  have hleftFar : ∑ y ∈ fareyLeftFar x, f y <= B := by
    exact fareyLeftFar_sum hQ hN x
  have hoffdiag : ∑ y ∈ (fareyIndices Q).erase x, f y <= 4 * B := by
    rw [hpartition]
    linarith
  have hdiag : f x <= 2 * (N : Real) := by
    simpa [f] using fejerKernel_le N 0
  have htotal := add_le_add hoffdiag hdiag
  have hdecomp := Finset.sum_erase_add (fareyIndices Q) f (mem_fareyIndices x)
  change (∑ y ∈ (fareyIndices Q).erase x, f y) + f x =
    ∑ y ∈ fareyIndices Q, f y at hdecomp
  calc
    ∑ y ∈ fareyIndices Q, f y =
        (∑ y ∈ (fareyIndices Q).erase x, f y) + f x := hdecomp.symm
    _ <= 4 * B + 2 * (N : Real) := htotal
    _ <= 18 * ((N : Real) + (Q : Real) ^ 2) := by
      dsimp [B]
      have hQreal : (0 : Real) < Q := by exact_mod_cast hQ
      field_simp [ne_of_gt hQreal]
      nlinarith

end BombieriVinogradov.LargeSieve
