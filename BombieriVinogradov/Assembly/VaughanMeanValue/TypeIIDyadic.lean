import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIIBlock
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Dyadic decomposition of Vaughan's Type II contribution

Canonical base-two blocks partition every active left coefficient. The exact
finite character sum is rewritten as efficient rectangular blocks, then its
maximal primitive-character mean is reduced to the sum of the proved block
majorants.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity

def dyadicExponentSet (X : Nat) : Finset Nat :=
  range (Nat.log 2 X + 1)

theorem dyadicExponent_mem_for {m X : Nat} (hm : 2 <= m) (hmX : m <= X) :
    let k := Nat.log 2 (m - 1)
    k ∈ dyadicExponentSet X ∧ 2 ^ k < m ∧ m <= 2 * 2 ^ k := by
  let k := Nat.log 2 (m - 1)
  have hmSub : Ne (m - 1) 0 := by omega
  have hpowLower : 2 ^ k <= m - 1 := by
    exact Nat.pow_log_le_self 2 hmSub
  have hpowUpper : m - 1 < 2 ^ (k + 1) := by
    simpa [k] using Nat.lt_pow_succ_log_self Nat.one_lt_two (m - 1)
  have hlogMono : k <= Nat.log 2 X := by
    apply Nat.log_mono_right
    omega
  have hsubLt : m - 1 < m := Nat.sub_lt (by omega) (by omega)
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlogMono), ?_, ?_⟩
  · exact hpowLower.trans_lt hsubLt
  · have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    have hmle : m <= 2 ^ (k + 1) := by
      rw [← hmEq]
      exact Nat.succ_le_iff.mpr hpowUpper
    simpa [pow_succ, mul_comm] using hmle

theorem dyadicExponent_unique {k m : Nat}
    (hblock : 2 ^ k < m ∧ m <= 2 * 2 ^ k) :
    Nat.log 2 (m - 1) = k := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · have hsubLt : m - 1 < m := Nat.sub_lt (by omega) (by omega)
    simpa [pow_succ, mul_comm] using hsubLt.trans_le hblock.2

theorem typeIILeftKernelCoefficient_eq_zero_of_le {u m : Nat} (hmu : m <= u) :
    typeIILeftKernelCoefficient u m = 0 := by
  unfold typeIILeftKernelCoefficient
  apply Finset.sum_eq_zero
  intro factors hfactors
  have hright : 0 < factors.2 := Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors)
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp hfactors).1
  have hleft : factors.1 <= m := by
    calc
      factors.1 <= factors.1 * factors.2 :=
        Nat.le_mul_of_pos_right factors.1 hright
      _ = m := hproduct
  simp [hleft.trans hmu]

theorem sum_typeIIBlockLeftCoefficient_eq (u X m : Nat)
    (hu : 1 <= u) (hmX : m <= X) :
    ∑ k ∈ dyadicExponentSet X, typeIIBlockLeftCoefficient u (2 ^ k) m =
      (typeIILeftKernelCoefficient u m : Complex) := by
  by_cases hmu : m <= u
  · have hzero := typeIILeftKernelCoefficient_eq_zero_of_le hmu
    simp [typeIIBlockLeftCoefficient, hzero]
  · have hm : 2 <= m := by omega
    let k₀ := Nat.log 2 (m - 1)
    have hk₀Data := dyadicExponent_mem_for hm hmX
    change k₀ ∈ dyadicExponentSet X ∧ 2 ^ k₀ < m ∧ m <= 2 * 2 ^ k₀ at hk₀Data
    rw [Finset.sum_eq_single k₀]
    · rw [typeIIBlockLeftCoefficient, if_pos hk₀Data.2]
    · intro k hk hne
      rw [typeIIBlockLeftCoefficient, if_neg]
      intro hblock
      apply hne
      exact (dyadicExponent_unique hblock).symm
    · intro hknot
      exact (hknot hk₀Data.1).elim

theorem Icc_one_div_eq_filter (Y m : Nat) (hm : 1 <= m) :
    Icc 1 (Y / m) = (Icc 1 Y).filter fun n => m * n <= Y := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · intro hn
    have hproduct : m * n <= Y := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp hn.2
      simpa [Nat.mul_comm] using this
    exact ⟨⟨hn.1, (Nat.le_mul_of_pos_left n (by omega)).trans hproduct⟩, hproduct⟩
  · intro hn
    refine ⟨hn.1.1, ?_⟩
    apply (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr
    simpa [Nat.mul_comm] using hn.2

theorem typeIICharacterSum_eq_restricted (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    typeIICharacterSum u v Y q chi =
      restrictedBilinearCharacterSum
        (fun m => (typeIILeftKernelCoefficient u m : Complex))
        (typeIIRightCoefficient v) Y Y Y q chi := by
  unfold typeIICharacterSum restrictedBilinearCharacterSum
  apply Finset.sum_congr rfl
  intro m hm
  rw [Icc_one_div_eq_filter Y m (Finset.mem_Icc.mp hm).1]
  rw [Finset.sum_filter]

def typeIIDyadicGlobalBlockSum (u v Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
    Y Y Y q chi

theorem typeIICharacterSum_eq_sum_dyadicGlobalBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    typeIICharacterSum u v Y q chi =
      ∑ k ∈ dyadicExponentSet X, typeIIDyadicGlobalBlockSum u v Y q k chi := by
  rw [typeIICharacterSum_eq_restricted]
  unfold typeIIDyadicGlobalBlockSum restrictedBilinearCharacterSum
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hproduct : m * n <= Y
  · simp only [hproduct, if_true]
    rw [← Finset.sum_mul]
    rw [← Finset.sum_mul]
    rw [sum_typeIIBlockLeftCoefficient_eq u X m hu
      ((Finset.mem_Icc.mp hm).2.trans hYX)]
  · simp [hproduct]

def typeIIBlockPairSet (M A B Y : Nat) : Finset (Nat × Nat) :=
  (Icc 1 A ×ˢ Icc 1 B).filter fun pair =>
    M < pair.1 ∧ pair.1 <= 2 * M ∧ pair.1 * pair.2 <= Y

def typeIIBlockPairSum (u v M A B Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ pair ∈ typeIIBlockPairSet M A B Y,
    (typeIILeftKernelCoefficient u pair.1 : Complex) * typeIIRightCoefficient v pair.2 *
      chi ((pair.1 * pair.2 : Nat) : ZMod q)

theorem restricted_typeIIBlock_eq_pairSum
    (u v M A B Y q : Nat) (chi : DirichletCharacter Complex q) :
    restrictedBilinearCharacterSum
        (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v)
        A B Y q chi = typeIIBlockPairSum u v M A B Y q chi := by
  unfold restrictedBilinearCharacterSum typeIIBlockPairSum typeIIBlockPairSet
  rw [← Finset.sum_product']
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pair hpair
  by_cases hsupport : M < pair.1 ∧ pair.1 <= 2 * M
  · by_cases hproduct : pair.1 * pair.2 <= Y
    · simp [hsupport, hproduct, typeIIBlockLeftCoefficient]
    · simp [hsupport, hproduct]
  · rw [typeIIBlockLeftCoefficient, if_neg hsupport]
    have hall : ¬(M < pair.1 ∧ pair.1 <= 2 * M ∧ pair.1 * pair.2 <= Y) := by
      intro h
      exact hsupport ⟨h.1, h.2.1⟩
    simp [hall]

theorem typeIIBlockPairSet_global_eq_efficient
    (M X Y : Nat) (hM : 1 <= M) (hYX : Y <= X) :
    typeIIBlockPairSet M Y Y Y = typeIIBlockPairSet M (2 * M) (X / M) Y := by
  ext pair
  unfold typeIIBlockPairSet
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro hpair
    have hMn : M * pair.2 <= pair.1 * pair.2 :=
      Nat.mul_le_mul_right pair.2 hpair.2.1.le
    have hnDiv : pair.2 <= X / M := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr
      simpa [Nat.mul_comm] using hMn.trans (hpair.2.2.2.trans hYX)
    exact ⟨⟨⟨hpair.1.1.1, hpair.2.2.1⟩, ⟨hpair.1.2.1, hnDiv⟩⟩,
      hpair.2⟩
  · intro hpair
    have hmpos : 0 < pair.1 := by omega
    have hnpos : 0 < pair.2 := by omega
    have hmY : pair.1 <= Y :=
      (Nat.le_mul_of_pos_right pair.1 hnpos).trans hpair.2.2.2
    have hnY : pair.2 <= Y :=
      (Nat.le_mul_of_pos_left pair.2 hmpos).trans hpair.2.2.2
    exact ⟨⟨⟨by omega, hmY⟩, ⟨by omega, hnY⟩⟩, hpair.2⟩

def typeIIDyadicBlockSum (u v X Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
    (2 * 2 ^ k) (X / 2 ^ k) Y q chi

theorem typeIIDyadicGlobalBlockSum_eq_blockSum
    (u v X Y q k : Nat) (chi : DirichletCharacter Complex q)
    (hYX : Y <= X) :
    typeIIDyadicGlobalBlockSum u v Y q k chi =
      typeIIDyadicBlockSum u v X Y q k chi := by
  unfold typeIIDyadicGlobalBlockSum typeIIDyadicBlockSum
  rw [restricted_typeIIBlock_eq_pairSum, restricted_typeIIBlock_eq_pairSum]
  unfold typeIIBlockPairSum
  have hpowOne : 1 <= 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega))
  rw [typeIIBlockPairSet_global_eq_efficient (2 ^ k) X Y hpowOne hYX]

theorem vaughanS3_eq_sum_dyadicBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    vaughanS3 u v Y (fun n => chi (n : ZMod q)) =
      ∑ k ∈ dyadicExponentSet X, typeIIDyadicBlockSum u v X Y q k chi := by
  rw [vaughanS3_eq_typeIICharacterSum]
  rw [typeIICharacterSum_eq_sum_dyadicGlobalBlocks u v X Y q chi hu hYX]
  apply Finset.sum_congr rfl
  intro k hk
  exact typeIIDyadicGlobalBlockSum_eq_blockSum u v X Y q k chi hYX

def maximalTypeIICharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖

theorem maximalTypeIICharacterNorm_le_sum_blocks
    (u v X q : Nat) (chi : DirichletCharacter Complex q) (hu : 1 <= u) :
    maximalTypeIICharacterNorm u v X q chi <=
      ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
  unfold maximalTypeIICharacterNorm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [vaughanS3_eq_sum_dyadicBlocks u v X Y q chi hu hYX]
  calc
    ‖∑ k ∈ dyadicExponentSet X, typeIIDyadicBlockSum u v X Y q k chi‖ <=
        ∑ k ∈ dyadicExponentSet X,
          ‖typeIIDyadicBlockSum u v X Y q k chi‖ := norm_sum_le _ _
    _ <= ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro k hk
      unfold typeIIDyadicBlockSum maximalBilinearNorm
      exact Finset.le_sup'
        (fun Z => ‖restrictedBilinearCharacterSum
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
          (2 * 2 ^ k) (X / 2 ^ k) Z q chi‖) hY

def typeIIDyadicMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeIICharacterNorm u v X q chi

theorem typeIIDyadicMean_le_sum_blockMeans
    (u v X Q : Nat) (hu : 1 <= u) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
  unfold typeIIDyadicMean
  calc
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, maximalTypeIICharacterNorm u v X q chi <=
      ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ∑ k ∈ dyadicExponentSet X,
            maximalBilinearNorm
              (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
              (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalTypeIICharacterNorm_le_sum_blocks u v X q chi hu
      · positivity
    _ = ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      unfold typeIIBlockMean
      let F : (q : Nat) -> DirichletCharacter Complex q -> Nat -> Real :=
        fun q chi k => maximalBilinearNorm
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
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
        _ = ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
            ((q : Real) / (q.totient : Real)) *
              ∑ chi ∈ primitiveCharacters q, F q chi k := by
          simp_rw [Finset.mul_sum]

def typeIIBlockMajorant (M N X Q : Nat) : Real :=
  (16 + 4 * Real.log ((X : Real) + 1)) *
    (Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) *
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real)))

theorem typeIIDyadicMean_le_sum_majorants
    (u v X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeIIDyadicMean u v X Q <=
        ∑ k ∈ dyadicExponentSet X,
          typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeIIDyadicMean_le_sum_blockMeans u v X Q hu
    _ <= ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [typeIIBlockMajorant] using
        typeIIBlockMean_le u v (2 ^ k) (X / 2 ^ k) X Q hX hQ

end BombieriVinogradov.VaughanMeanValue
