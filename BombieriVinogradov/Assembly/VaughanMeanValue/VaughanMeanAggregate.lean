import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanMeanBound
import Mathlib.Tactic

/-!
# Pre-optimization Vaughan mean estimate

The maximal first Type I term is aggregated over primitive characters, then
all four corrected Vaughan contributions are combined with one symbolic cutoff.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve

def typeIOneMaximalMean (v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi

theorem weighted_primitive_maximalVaughanS1_le {q : Nat} [NeZero q]
    (hq : 1 < q) (v X : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi <=
      (q : Real) * (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((X + 1 : Nat) : Real)) := by
  classical
  let B : Real := (v : Real) *
    (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
      Real.log ((X + 1 : Nat) : Real))
  have hB : 0 <= B := by
    dsimp [B]
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
      linarith
    positivity
  have hchars :
      ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi <=
        (q.totient : Real) * B := by
    calc
      _ <= ∑ chi ∈ primitiveCharacters q, B := by
        apply Finset.sum_le_sum
        intro chi hchiMem
        have hchi : DirichletCharacter.IsPrimitive chi := by
          simpa [primitiveCharacters] using (Finset.mem_filter.mp hchiMem).2
        exact maximalVaughanS1Norm_le hq hchi v X
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

def nontrivialTypeIOneMaximalMean (v X Q : Nat) : Real :=
  ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi

theorem nontrivialTypeIOneMaximalMean_le (v X Q : Nat) :
    nontrivialTypeIOneMaximalMean v X Q <=
      4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
        Real.log (2 * (Q : Real)) * Real.log ((X + 1 : Nat) : Real) := by
  let D : Real := (Q : Real) * (v : Real) *
    (4 * Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) *
      Real.log ((X + 1 : Nat) : Real))
  have hD : 0 <= D := by
    dsimp [D]
    by_cases hQ : Q = 0
    · simp [hQ]
    · have hlogQ : 0 <= Real.log (2 * (Q : Real)) := by
        apply Real.log_nonneg
        have : (1 : Real) <= (Q : Real) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
        linarith
      positivity
  have hterm : ∀ q ∈ Icc 2 Q,
      ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi <= D := by
    intro q hqMem
    have hqBounds := Finset.mem_Icc.mp hqMem
    let _ : NeZero q := ⟨(by omega)⟩
    apply (weighted_primitive_maximalVaughanS1_le (show 1 < q by omega) v X).trans
    dsimp [D]
    have hqcast : (q : Real) <= (Q : Real) := by exact_mod_cast hqBounds.2
    have hsqrt := Real.sqrt_le_sqrt hqcast
    have hlog : Real.log (2 * (q : Real)) <= Real.log (2 * (Q : Real)) := by
      apply Real.log_le_log
      · exact mul_pos (by norm_num) (by exact_mod_cast (show 0 < q by omega))
      · nlinarith
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast (show 1 <= q by omega)
      linarith
    have hlogX : 0 <= Real.log ((X + 1 : Nat) : Real) :=
      Real.log_natCast_nonneg (X + 1)
    gcongr
  unfold nontrivialTypeIOneMaximalMean
  calc
    _ <= ∑ q ∈ Icc 2 Q, D := Finset.sum_le_sum hterm
    _ = ((Icc 2 Q).card : Real) * D := by simp
    _ <= (Q : Real) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show (Icc 2 Q).card <= Q by simp)
    _ = _ := by dsimp [D]; ring

theorem typeIOneMaximalMean_le (v X Q : Nat) (hQ : 1 <= Q) :
    typeIOneMaximalMean v X Q <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          Real.log (2 * (Q : Real)) * Real.log ((X + 1 : Nat) : Real) := by
  have hlevel :
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1, maximalVaughanS1Norm v X 1 chi <=
        3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
    let B : Real := 3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2
    have hB : 0 <= B := by dsimp [B]; positivity
    have hsum : ∑ chi ∈ primitiveCharacters 1, maximalVaughanS1Norm v X 1 chi <= B := by
      calc
        _ <= ∑ chi ∈ primitiveCharacters 1, B := by
          apply Finset.sum_le_sum
          intro chi hchi
          exact maximalVaughanS1Norm_trivial v X 1 chi
        _ = ((primitiveCharacters 1).card : Real) * B := by simp
        _ <= B := by
          have hcard : ((primitiveCharacters 1).card : Real) <= 1 := by
            exact_mod_cast primitiveCharacters_card_le_totient 1
          nlinarith
    norm_num
    simpa [B] using hsum
  have hsplit : typeIOneMaximalMean v X Q =
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1, maximalVaughanS1Norm v X 1 chi +
        nontrivialTypeIOneMaximalMean v X Q := by
    unfold typeIOneMaximalMean nontrivialTypeIOneMaximalMean
    rw [← Finset.insert_Icc_succ_left_eq_Icc hQ]
    rw [Finset.sum_insert (by simp)]
    simp
  rw [hsplit]
  exact add_le_add hlevel (nontrivialTypeIOneMaximalMean_le v X Q)

def vaughanMean (X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalMangoldtCharacterNorm X q chi

theorem vaughanMean_le_parts (u X Q : Nat) :
    vaughanMean X Q <=
      typeIOneMaximalMean u X Q + typeITwoMean u u X Q +
        typeIIDyadicMean u u X Q + vaughanS4Mean u X Q := by
  unfold vaughanMean typeIOneMaximalMean typeITwoMean typeIIDyadicMean vaughanS4Mean
  calc
    _ <= ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          (maximalVaughanS1Norm u X q chi +
            maximalTypeITwoCharacterNorm u u X q chi +
              maximalTypeIICharacterNorm u u X q chi + maximalVaughanS4Norm u X q chi) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalMangoldtCharacterNorm_le_parts u u X q chi
      · positivity
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, mul_add]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]

theorem vaughanMean_le_preoptimized
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    vaughanMean X Q <=
      (3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        4 * (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          Real.log (2 * (Q : Real)) * Real.log ((X + 1 : Nat) : Real)) +
      (3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
          Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) +
        11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q) +
      (11520 * Real.log (X : Real) ^ 3 * typeIISourceCore X u Q) +
      ((u : Real) * (Q : Real) ^ 2 * Real.log ((u + 1 : Nat) : Real)) := by
  exact (vaughanMean_le_parts u X Q).trans
    (add_le_add
      (add_le_add
        (add_le_add (typeIOneMaximalMean_le u X Q hQ)
          (typeITwoMean_le_hybrid u X Q hu hX hQ))
        (typeIIDyadicMean_le_sourceScale u X Q hu hX hQ))
      (vaughanS4Mean_le u X Q))

end BombieriVinogradov.VaughanMeanValue
