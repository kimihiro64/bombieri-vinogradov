import BombieriVinogradov.Proof.LargeSieve.Duality
import BombieriVinogradov.Proof.LargeSieve.FareyRow
import Mathlib.Tactic

/-!
# Doubled-window smooth majorant

The doubled rectangular window has a triangular autocorrelation.  Dividing
its Gram matrix by the original interval length produces exactly the Fejer
kernel used in the additive large sieve.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

/-- The two-window additive phase matrix. -/
def doubledPhaseMatrix {ι : Type*} (L : Nat) (x : ι -> Real)
    (r : Fin L × Fin L) (i : ι) : Complex :=
  additivePhase ((r.1 : Nat) * x i) * additivePhase (-((r.2 : Nat) * x i))

theorem doubledPhase_gram {ι : Type*} (L : Nat) (x : ι -> Real) (i j : ι) :
    ∑ r : Fin L × Fin L,
        conj (doubledPhaseMatrix L x r i) * doubledPhaseMatrix L x r j =
      phaseSum L (x j - x i) * conj (phaseSum L (x j - x i)) := by
  rw [Fintype.sum_prod_type]
  simp_rw [doubledPhaseMatrix, map_mul, conj_additivePhase]
  simp only [neg_neg]
  have hterm (u v : Fin L) :
      (additivePhase (-((u : Nat) * x i)) * additivePhase ((v : Nat) * x i)) *
          (additivePhase ((u : Nat) * x j) * additivePhase (-((v : Nat) * x j))) =
        additivePhase ((u : Nat) * (x j - x i)) *
          additivePhase (-((v : Nat) * (x j - x i))) := by
    calc
      (additivePhase (-((u : Nat) * x i)) * additivePhase ((v : Nat) * x i)) *
          (additivePhase ((u : Nat) * x j) * additivePhase (-((v : Nat) * x j))) =
        additivePhase (-((u : Nat) * x i) + (v : Nat) * x i) *
          additivePhase ((u : Nat) * x j + (-((v : Nat) * x j))) := by
            rw [additivePhase_add, additivePhase_add]
      _ = additivePhase
          ((-((u : Nat) * x i) + (v : Nat) * x i) +
            ((u : Nat) * x j + (-((v : Nat) * x j)))) :=
        (additivePhase_add _ _).symm
      _ = additivePhase
          ((u : Nat) * (x j - x i) + (-((v : Nat) * (x j - x i)))) := by
        congr 1
        ring
      _ = additivePhase ((u : Nat) * (x j - x i)) *
          additivePhase (-((v : Nat) * (x j - x i))) := additivePhase_add _ _
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hpos : (∑ u : Fin L, additivePhase ((u : Nat) * (x j - x i))) =
      phaseSum L (x j - x i) := by
    rw [phaseSum]
    exact (Finset.sum_range (fun u => additivePhase ((u : Real) * (x j - x i)))).symm
  have hneg : (∑ v : Fin L, additivePhase (-((v : Nat) * (x j - x i)))) =
      conj (phaseSum L (x j - x i)) := by
    calc
      (∑ v : Fin L, additivePhase (-((v : Nat) * (x j - x i)))) =
          ∑ v : Fin L, conj (additivePhase ((v : Nat) * (x j - x i))) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [conj_additivePhase]
      _ = conj (∑ v : Fin L, additivePhase ((v : Nat) * (x j - x i))) := by
        rw [map_sum]
      _ = conj (phaseSum L (x j - x i)) := by rw [hpos]
  rw [hpos, hneg]

theorem norm_doubledPhase_gram {ι : Type*} {N : Nat} (hN : 0 < N)
    (x : ι -> Real) (i j : ι) :
    ‖∑ r : Fin (2 * N) × Fin (2 * N),
        conj (doubledPhaseMatrix (2 * N) x r i) *
          doubledPhaseMatrix (2 * N) x r j‖ =
      (N : Real) * fejerKernel (2 * N) (x j - x i) := by
  rw [doubledPhase_gram, norm_mul, norm_conj]
  unfold fejerKernel
  have hNreal : Ne (N : Real) 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp [hNreal]

/-- The doubled-window dual energy over Farey points is `O(N * (N + Q^2))`. -/
theorem fareyDoubledWindowEnergy {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (b : FareyIndex Q -> Complex) :
    ∑ r ∈ (Finset.univ : Finset (Fin (2 * N) × Fin (2 * N))),
        ‖∑ i ∈ fareyIndices Q,
          doubledPhaseMatrix (2 * N)
            (fun y => (fareyValue y : Real)) r i * b i‖ ^ 2 <=
      ((N : Real) * 18 * ((2 * N : Nat) + (Q : Real) ^ 2)) *
        ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 := by
  let xv : FareyIndex Q -> Real := fun y => (fareyValue y : Real)
  let k : FareyIndex Q -> FareyIndex Q -> Real := fun i j =>
    (N : Real) * fejerKernel (2 * N) (xv j - xv i)
  apply complexGramSchurBoundFinset
    (Finset.univ : Finset (Fin (2 * N) × Fin (2 * N)))
    (fareyIndices Q) (doubledPhaseMatrix (2 * N) xv) b k
  · intro i hi j hj
    dsimp [k]
    exact mul_nonneg (Nat.cast_nonneg N) (fejerKernel_nonneg _ _)
  · intro i hi j hj
    dsimp [k, xv]
    congr 1
    rw [show (fareyValue j : Real) - (fareyValue i : Real) =
      -((fareyValue i : Real) - (fareyValue j : Real)) by ring, fejerKernel_neg]
  · intro i hi
    have hrow := fareyFejerRowSum hQ
      (Nat.mul_pos (by norm_num : 0 < 2) hN) i
    dsimp [k, xv]
    calc
      ∑ j ∈ fareyIndices Q, (N : Real) *
          fejerKernel (2 * N) ((fareyValue j : Real) - (fareyValue i : Real)) =
        (N : Real) * ∑ j ∈ fareyIndices Q,
          fejerKernel (2 * N) ((fareyValue j : Real) - (fareyValue i : Real)) := by
            rw [Finset.mul_sum]
      _ = (N : Real) * ∑ j ∈ fareyIndices Q,
          fejerKernel (2 * N) ((fareyValue i : Real) - (fareyValue j : Real)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (fareyValue j : Real) - (fareyValue i : Real) =
          -((fareyValue i : Real) - (fareyValue j : Real)) by ring, fejerKernel_neg]
      _ <= (N : Real) *
          (18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2)) := by
        gcongr
      _ = (N : Real) * 18 * ((2 * N : Nat) + (Q : Real) ^ 2) := by ring
  · intro i hi j hj
    simpa using (norm_doubledPhase_gram hN xv i j).le

/-- The dual additive sum at one nonnegative frequency. -/
def fareyDualSample {Q : Nat} (b : FareyIndex Q -> Complex) (n : Nat) : Complex :=
  ∑ i ∈ fareyIndices Q,
    additivePhase ((n : Real) * (fareyValue i : Real)) * b i

/-- Embed an original frequency and one averaging shift into the doubled window. -/
def doubledWindowEmbedding (N : Nat) :
    Fin N × Fin N -> Fin (2 * N) × Fin (2 * N) := fun p =>
  (⟨p.1.1 + p.2.1, by omega⟩, ⟨p.2.1, by omega⟩)

theorem doubledWindowEmbedding_injective (N : Nat) :
    Function.Injective (doubledWindowEmbedding N) := by
  intro p q hpq
  have hsecond : p.2.1 = q.2.1 := congrArg (fun z => z.2.1) hpq
  have hfirst : p.1.1 + p.2.1 = q.1.1 + q.2.1 :=
    congrArg (fun z => z.1.1) hpq
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    exact hsecond

theorem doubledWindowEmbedding_apply {Q N : Nat}
    (b : FareyIndex Q -> Complex) (p : Fin N × Fin N) :
    ∑ i ∈ fareyIndices Q,
        doubledPhaseMatrix (2 * N) (fun y => (fareyValue y : Real))
          (doubledWindowEmbedding N p) i * b i =
      fareyDualSample b p.1.1 := by
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [doubledPhaseMatrix, doubledWindowEmbedding, fareyDualSample]
  congr 1
  rw [← additivePhase_add]
  congr 1
  push_cast
  ring

/-- Averaging the doubled window majorizes the original dual interval energy. -/
theorem fareyDualSample_le_doubledWindow {Q N : Nat}
    (b : FareyIndex Q -> Complex) :
    (N : Real) * ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      ∑ r : Fin (2 * N) × Fin (2 * N),
        ‖∑ i ∈ fareyIndices Q,
          doubledPhaseMatrix (2 * N) (fun y => (fareyValue y : Real)) r i * b i‖ ^ 2 := by
  let g : (Fin (2 * N) × Fin (2 * N)) -> Real := fun r =>
    ‖∑ i ∈ fareyIndices Q,
      doubledPhaseMatrix (2 * N) (fun y => (fareyValue y : Real)) r i * b i‖ ^ 2
  have hinj := doubledWindowEmbedding_injective N
  have hle := sum_comp_le_sum_of_injective (doubledWindowEmbedding N) hinj g
    (fun r => sq_nonneg _)
  have heq : ∑ p : Fin N × Fin N, g (doubledWindowEmbedding N p) =
      (N : Real) * ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [g, doubledWindowEmbedding_apply]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [← heq]
  exact hle

/-- The source-scale dual additive large-sieve bound. -/
theorem fareyDualEnergy {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (b : FareyIndex Q -> Complex) :
    ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 := by
  have hmajor := fareyDualSample_le_doubledWindow (N := N) b
  have hwindow := fareyDoubledWindowEnergy hQ hN b
  have hmul : (N : Real) * ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      (N : Real) *
        (18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2) *
          ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2) := by
    exact hmajor.trans (by simpa [mul_assoc] using hwindow)
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hbase : ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2) *
        ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 :=
    (mul_le_mul_iff_of_pos_left hNreal).mp hmul
  apply hbase.trans
  have hmass : 0 <= ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 := by positivity
  have hcoef : 18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2) <=
      36 * ((N : Real) + (Q : Real) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg (Q : Real)]
  exact mul_le_mul_of_nonneg_right hcoef hmass

/-- The coefficient-side additive sum at one Farey point. -/
def fareyAdditiveSample {Q : Nat} (a : Nat -> Complex) (N : Nat)
    (i : FareyIndex Q) : Complex :=
  ∑ n ∈ range N,
    a n * additivePhase ((n : Real) * (fareyValue i : Real))

theorem fareyAdditive_duality {Q N : Nat} (a : Nat -> Complex) :
    (((∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2 : Real) : Real) :
        Complex) =
      ∑ n ∈ range N, a n *
        fareyDualSample (Q := Q)
          (fun i : FareyIndex Q => conj (fareyAdditiveSample (Q := Q) a N i)) n := by
  have hterm (z : Complex) : ((‖z‖ ^ 2 : Real) : Complex) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_sum]
  simp_rw [hterm, fareyAdditiveSample, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [fareyDualSample, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The additive large sieve for all reduced fractions of level at most `Q`. -/
theorem additiveLargeSieve {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (a : Nat -> Complex) :
    ∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2 <=
      36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  let S : FareyIndex Q -> Complex := fun i => fareyAdditiveSample a N i
  let E : Real := ∑ i ∈ fareyIndices Q, ‖S i‖ ^ 2
  let mass : Real := ∑ n ∈ range N, ‖a n‖ ^ 2
  let b : FareyIndex Q -> Complex := fun i => conj (S i)
  let T : Nat -> Complex := fun n => fareyDualSample b n
  let B : Real := 36 * ((N : Real) + (Q : Real) ^ 2)
  have hE0 : 0 <= E := by dsimp [E]; positivity
  have hid := fareyAdditive_duality (Q := Q) (N := N) a
  change (E : Complex) = ∑ n ∈ range N, a n * T n at hid
  have hnorm : E = ‖∑ n ∈ range N, a n * T n‖ := by
    calc
      E = ‖(E : Complex)‖ := by simp [abs_of_nonneg hE0]
      _ = ‖∑ n ∈ range N, a n * T n‖ := congrArg norm hid
  have htri : E <= ∑ n ∈ range N, ‖a n‖ * ‖T n‖ := by
    calc
      E = ‖∑ n ∈ range N, a n * T n‖ := hnorm
      _ <= ∑ n ∈ range N, ‖a n * T n‖ := norm_sum_le _ _
      _ = ∑ n ∈ range N, ‖a n‖ * ‖T n‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul]
  have hsq : E ^ 2 <= (∑ n ∈ range N, ‖a n‖ * ‖T n‖) ^ 2 :=
    pow_le_pow_left₀ hE0 htri 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range N)
    (fun n => ‖a n‖) (fun n => ‖T n‖)
  have hpre : E ^ 2 <= mass * ∑ n ∈ range N, ‖T n‖ ^ 2 := by
    exact hsq.trans (by simpa [mass] using hcs)
  have hdualFin := fareyDualEnergy hQ hN b
  have hdual : ∑ n ∈ range N, ‖T n‖ ^ 2 <= B * E := by
    rw [Finset.sum_range]
    simpa [T, B, b, E] using hdualFin
  have hmass0 : 0 <= mass := by dsimp [mass]; positivity
  have hE2 : E ^ 2 <= mass * (B * E) :=
    hpre.trans (mul_le_mul_of_nonneg_left hdual hmass0)
  by_cases hEz : E = 0
  · change E <= B * mass
    rw [hEz]
    dsimp [B, mass]
    positivity
  · have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEz)
    have hcancel : E <= mass * B := by
      apply (mul_le_mul_iff_of_pos_right hEpos).mp
      nlinarith [hE2]
    change E <= B * mass
    nlinarith

end BombieriVinogradov.LargeSieve
