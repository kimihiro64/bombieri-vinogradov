import BombieriVinogradov.Assembly.VaughanMeanValue.TypeITwoBlock
import Mathlib.Tactic

/-!
# Dyadic decomposition of the large part of Vaughan's second Type I term

The exact large-factor sum is partitioned into canonical base-two blocks and
rewritten using efficient rectangles for the maximal bilinear estimate.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

def typeITwoLargeCoefficient (u v m : Nat) : Complex :=
  if u < m then (typeITwoKernelCoefficient u v m : Complex) else 0

theorem sum_typeITwoBlockLeftCoefficient_eq (u v X m : Nat)
    (hu : 1 <= u) (hmX : m <= X) :
    ∑ k ∈ dyadicExponentSet X, typeITwoBlockLeftCoefficient u v (2 ^ k) m =
      typeITwoLargeCoefficient u v m := by
  by_cases hmu : m <= u
  · simp [typeITwoBlockLeftCoefficient, typeITwoLargeCoefficient,
      not_lt.mpr hmu]
  · have hm : 2 <= m := by omega
    let k₀ := Nat.log 2 (m - 1)
    have hk₀Data := dyadicExponent_mem_for hm hmX
    change k₀ ∈ dyadicExponentSet X ∧ 2 ^ k₀ < m ∧ m <= 2 * 2 ^ k₀ at hk₀Data
    rw [Finset.sum_eq_single k₀]
    · rw [typeITwoBlockLeftCoefficient,
        if_pos ⟨lt_of_not_ge hmu, hk₀Data.2⟩,
        typeITwoLargeCoefficient, if_pos (lt_of_not_ge hmu)]
    · intro k hk hne
      rw [typeITwoBlockLeftCoefficient, if_neg]
      intro hblock
      apply hne
      exact (dyadicExponent_unique hblock.2).symm
    · intro hknot
      exact (hknot hk₀Data.1).elim

theorem typeITwoLargeCharacterSum_eq_restricted (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    typeITwoLargeCharacterSum u v Y q chi =
      restrictedBilinearCharacterSum
        (typeITwoLargeCoefficient u v) typeITwoRightCoefficient Y Y Y q chi := by
  unfold typeITwoLargeCharacterSum restrictedBilinearCharacterSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Icc_one_div_eq_filter Y m (Finset.mem_Icc.mp hm).1]
  rw [Finset.sum_filter]
  by_cases hmu : u < m
  · simp [hmu, typeITwoLargeCoefficient, typeITwoRightCoefficient]
  · simp [hmu, typeITwoLargeCoefficient]

def typeITwoDyadicGlobalBlockSum (u v Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
    Y Y Y q chi

theorem typeITwoLargeCharacterSum_eq_sum_globalBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    typeITwoLargeCharacterSum u v Y q chi =
      ∑ k ∈ dyadicExponentSet X, typeITwoDyadicGlobalBlockSum u v Y q k chi := by
  rw [typeITwoLargeCharacterSum_eq_restricted]
  unfold typeITwoDyadicGlobalBlockSum restrictedBilinearCharacterSum
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hproduct : m * n <= Y
  · simp only [hproduct, if_true, typeITwoRightCoefficient]
    simp_rw [mul_one]
    rw [← Finset.sum_mul]
    rw [sum_typeITwoBlockLeftCoefficient_eq u v X m hu
      ((Finset.mem_Icc.mp hm).2.trans hYX)]
  · simp [hproduct]

def typeITwoBlockPairSum (u v M A B Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ pair ∈ typeIIBlockPairSet M A B Y,
    typeITwoLargeCoefficient u v pair.1 *
      chi ((pair.1 * pair.2 : Nat) : ZMod q)

theorem restricted_typeITwoBlock_eq_pairSum
    (u v M A B Y q : Nat) (chi : DirichletCharacter Complex q) :
    restrictedBilinearCharacterSum
        (typeITwoBlockLeftCoefficient u v M) typeITwoRightCoefficient
        A B Y q chi = typeITwoBlockPairSum u v M A B Y q chi := by
  unfold restrictedBilinearCharacterSum typeITwoBlockPairSum typeIIBlockPairSet
  rw [← Finset.sum_product']
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pair hpair
  by_cases hblock : M < pair.1 ∧ pair.1 <= 2 * M
  · by_cases hlarge : u < pair.1
    · have hsupport : u < pair.1 ∧ M < pair.1 ∧ pair.1 <= 2 * M :=
        ⟨hlarge, hblock⟩
      by_cases hproduct : pair.1 * pair.2 <= Y
      · simp [hsupport, hproduct, typeITwoBlockLeftCoefficient,
          typeITwoLargeCoefficient, typeITwoRightCoefficient]
      · simp [hsupport, hproduct]
    · have hsupport : ¬(u < pair.1 ∧ M < pair.1 ∧ pair.1 <= 2 * M) := by
        exact fun h => hlarge h.1
      simp [hlarge, typeITwoBlockLeftCoefficient,
        typeITwoLargeCoefficient]
  · have hsupport : ¬(u < pair.1 ∧ M < pair.1 ∧ pair.1 <= 2 * M) := by
      exact fun h => hblock h.2
    rw [typeITwoBlockLeftCoefficient, if_neg hsupport]
    have hall : ¬(M < pair.1 ∧ pair.1 <= 2 * M ∧ pair.1 * pair.2 <= Y) := by
      intro h
      exact hblock ⟨h.1, h.2.1⟩
    simp [hall]

def typeITwoDyadicBlockSum (u v X Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
    (2 * 2 ^ k) (X / 2 ^ k) Y q chi

theorem typeITwoDyadicGlobalBlockSum_eq_blockSum
    (u v X Y q k : Nat) (chi : DirichletCharacter Complex q)
    (hYX : Y <= X) :
    typeITwoDyadicGlobalBlockSum u v Y q k chi =
      typeITwoDyadicBlockSum u v X Y q k chi := by
  unfold typeITwoDyadicGlobalBlockSum typeITwoDyadicBlockSum
  rw [restricted_typeITwoBlock_eq_pairSum, restricted_typeITwoBlock_eq_pairSum]
  unfold typeITwoBlockPairSum
  have hpowOne : 1 <= 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega))
  rw [typeIIBlockPairSet_global_eq_efficient (2 ^ k) X Y hpowOne hYX]

theorem typeITwoLargeCharacterSum_eq_sum_dyadicBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    typeITwoLargeCharacterSum u v Y q chi =
      ∑ k ∈ dyadicExponentSet X, typeITwoDyadicBlockSum u v X Y q k chi := by
  rw [typeITwoLargeCharacterSum_eq_sum_globalBlocks u v X Y q chi hu hYX]
  apply Finset.sum_congr rfl
  intro k hk
  exact typeITwoDyadicGlobalBlockSum_eq_blockSum u v X Y q k chi hYX

def maximalTypeITwoLargeCharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖typeITwoLargeCharacterSum u v Y q chi‖

theorem maximalTypeITwoLargeCharacterNorm_le_sum_blocks
    (u v X q : Nat) (chi : DirichletCharacter Complex q) (hu : 1 <= u) :
    maximalTypeITwoLargeCharacterNorm u v X q chi <=
      ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
  unfold maximalTypeITwoLargeCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [typeITwoLargeCharacterSum_eq_sum_dyadicBlocks u v X Y q chi hu hYX]
  calc
    _ <= ∑ k ∈ dyadicExponentSet X,
        ‖typeITwoDyadicBlockSum u v X Y q k chi‖ := norm_sum_le _ _
    _ <= ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro k hk
      unfold typeITwoDyadicBlockSum maximalBilinearNorm
      exact Finset.le_sup'
        (fun Z => ‖restrictedBilinearCharacterSum
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) Z q chi‖) hY

end BombieriVinogradov.VaughanMeanValue
