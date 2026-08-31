import BombieriVinogradov.Proof.LargeSieve.Schur
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Finite complex Gram duality

This module lifts the real Schur bound to a finite complex matrix.  It is the
linear-algebra step in the dual form of the additive large sieve.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

theorem complexEnergy_eq_gram {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : ρ -> ι -> Complex) (b : ι -> Complex) :
    (((∑ r, ‖∑ i, A r i * b i‖ ^ 2 : Real) : Real) : Complex) =
      ∑ i, ∑ j, conj (b i) * b j *
        ∑ r, conj (A r i) * A r j := by
  have hterm (z : Complex) : ((‖z‖ ^ 2 : Real) : Complex) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_sum]
  simp_rw [hterm]
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- A complex Gram matrix inherits the largest-row Schur bound. -/
theorem complexGramSchurBound {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : ρ -> ι -> Complex) (b : ι -> Complex)
    (k : ι -> ι -> Real)
    (hk : ∀ i j, 0 <= k i j) (hsymm : ∀ i j, k i j = k j i)
    {B : Real} (hrow : ∀ i, ∑ j, k i j <= B)
    (hgram : ∀ i j, ‖∑ r, conj (A r i) * A r j‖ <= k i j) :
    ∑ r, ‖∑ i, A r i * b i‖ ^ 2 <= B * ∑ i, ‖b i‖ ^ 2 := by
  let G : Complex := ∑ i, ∑ j, conj (b i) * b j *
    ∑ r, conj (A r i) * A r j
  have henergy := complexEnergy_eq_gram A b
  change ((∑ r, ‖∑ i, A r i * b i‖ ^ 2 : Real) : Complex) = G at henergy
  have hre : ∑ r, ‖∑ i, A r i * b i‖ ^ 2 = G.re := by
    calc
      ∑ r, ‖∑ i, A r i * b i‖ ^ 2 =
          (((∑ r, ‖∑ i, A r i * b i‖ ^ 2 : Real) : Complex)).re :=
        (Complex.ofReal_re _).symm
      _ = G.re := congrArg Complex.re henergy
  calc
    ∑ r, ‖∑ i, A r i * b i‖ ^ 2 = G.re := hre
    _ <= ‖G‖ := Complex.re_le_norm G
    _ <= ∑ i, ‖∑ j, conj (b i) * b j *
          ∑ r, conj (A r i) * A r j‖ := by
      exact norm_sum_le _ _
    _ <= ∑ i, ∑ j, ‖conj (b i) * b j *
          ∑ r, conj (A r i) * A r j‖ := by
      exact Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ = ∑ i, ∑ j, ‖b i‖ * ‖b j‖ *
          ‖∑ r, conj (A r i) * A r j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [norm_mul, norm_conj]
    _ <= ∑ i, ∑ j, ‖b i‖ * ‖b j‖ * k i j := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hgram i j)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ <= B * ∑ i, ‖b i‖ ^ 2 :=
      schurBound k hk hsymm hrow (fun i => ‖b i‖)

theorem complexEnergyFinset_eq_gram {ρ ι : Type*}
    [DecidableEq ρ] [DecidableEq ι] (sr : Finset ρ) (si : Finset ι)
    (A : ρ -> ι -> Complex) (b : ι -> Complex) :
    (((∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 : Real) : Real) : Complex) =
      ∑ i ∈ si, ∑ j ∈ si, conj (b i) * b j *
        ∑ r ∈ sr, conj (A r i) * A r j := by
  have hterm (z : Complex) : ((‖z‖ ^ 2 : Real) : Complex) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_sum]
  simp_rw [hterm]
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Finset-indexed complex Gram/Schur bound. -/
theorem complexGramSchurBoundFinset {ρ ι : Type*}
    [DecidableEq ρ] [DecidableEq ι] (sr : Finset ρ) (si : Finset ι)
    (A : ρ -> ι -> Complex) (b : ι -> Complex)
    (k : ι -> ι -> Real)
    (hk : ∀ i ∈ si, ∀ j ∈ si, 0 <= k i j)
    (hsymm : ∀ i ∈ si, ∀ j ∈ si, k i j = k j i)
    {B : Real} (hrow : ∀ i ∈ si, ∑ j ∈ si, k i j <= B)
    (hgram : ∀ i ∈ si, ∀ j ∈ si,
      ‖∑ r ∈ sr, conj (A r i) * A r j‖ <= k i j) :
    ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 <=
      B * ∑ i ∈ si, ‖b i‖ ^ 2 := by
  let G : Complex := ∑ i ∈ si, ∑ j ∈ si, conj (b i) * b j *
    ∑ r ∈ sr, conj (A r i) * A r j
  have henergy := complexEnergyFinset_eq_gram sr si A b
  change ((∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 : Real) : Complex) = G at henergy
  have hre : ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 = G.re := by
    calc
      ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 =
          (((∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 : Real) : Complex)).re :=
        (Complex.ofReal_re _).symm
      _ = G.re := congrArg Complex.re henergy
  calc
    ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 = G.re := hre
    _ <= ‖G‖ := Complex.re_le_norm G
    _ <= ∑ i ∈ si, ‖∑ j ∈ si, conj (b i) * b j *
          ∑ r ∈ sr, conj (A r i) * A r j‖ := by
      exact norm_sum_le _ _
    _ <= ∑ i ∈ si, ∑ j ∈ si, ‖conj (b i) * b j *
          ∑ r ∈ sr, conj (A r i) * A r j‖ := by
      exact Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ = ∑ i ∈ si, ∑ j ∈ si, ‖b i‖ * ‖b j‖ *
          ‖∑ r ∈ sr, conj (A r i) * A r j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [norm_mul, norm_conj]
    _ <= ∑ i ∈ si, ∑ j ∈ si, ‖b i‖ * ‖b j‖ * k i j := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hgram i hi j hj)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ <= B * ∑ i ∈ si, ‖b i‖ ^ 2 :=
      schurBoundFinset si k hk hsymm hrow (fun i => ‖b i‖)

/-- An injective reindexing of a nonnegative finite sum is bounded by the full target sum. -/
theorem sum_comp_le_sum_of_injective {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (e : α -> β) (he : Function.Injective e)
    (g : β -> Real) (hg : ∀ b, 0 <= g b) :
    ∑ a, g (e a) <= ∑ b, g b := by
  have hsubset : Finset.univ.image e ⊆ (Finset.univ : Finset β) := by
    exact fun b hb => Finset.mem_univ b
  calc
    ∑ a, g (e a) = ∑ b ∈ Finset.univ.image e, g b :=
      (Finset.sum_image he.injOn).symm
    _ <= ∑ b, g b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro b hb hnot
        exact hg b)

end BombieriVinogradov.LargeSieve
