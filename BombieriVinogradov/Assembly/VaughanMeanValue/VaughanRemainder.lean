import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIOne
import BombieriVinogradov.Proof.VaughanIdentity.Main
import Mathlib.Tactic

/-!
# The truncated Vaughan remainder

The short von-Mangoldt head is bounded termwise and summed over primitive
characters, including the exact maximal endpoint convention.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity

theorem norm_vaughanS4_le (u Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ <=
      (u : Real) * Real.log ((u + 1 : Nat) : Real) := by
  let active : Finset Nat := (Icc 1 Y).filter fun n => n <= u
  have hterm : ∀ n ∈ active,
      ‖(ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)‖ <=
        Real.log ((u + 1 : Nat) : Real) := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnData.1).1
    calc
      _ = ArithmeticFunction.vonMangoldt n * ‖chi (n : ZMod q)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ <= Real.log (n : Real) * 1 := by
        exact mul_le_mul ArithmeticFunction.vonMangoldt_le_log
          (DirichletCharacter.norm_le_one chi (n : ZMod q))
          (norm_nonneg _) (Real.log_natCast_nonneg n)
      _ <= Real.log ((u + 1 : Nat) : Real) := by
        rw [mul_one]
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast Nat.le_succ_of_le hnData.2
  have hactive : active ⊆ Icc 1 u := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnData.1).1, hnData.2⟩
  unfold vaughanS4 weightedKernelSum lambdaHead truncateLE
  change ‖∑ n ∈ Icc 1 Y,
      ((if n <= u then ArithmeticFunction.vonMangoldt n else 0 : Real) : Complex) *
        chi (n : ZMod q)‖ <= _
  have hrewrite :
      (∑ n ∈ Icc 1 Y,
        ((if n <= u then ArithmeticFunction.vonMangoldt n else 0 : Real) : Complex) *
          chi (n : ZMod q)) =
        ∑ n ∈ active,
          (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q) := by
    unfold active
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnu : n <= u <;> simp [hnu]
  rw [hrewrite]
  change ‖∑ n ∈ active,
      (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)‖ <= _
  calc
    _ <= ∑ n ∈ active,
        ‖(ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)‖ :=
      norm_sum_le _ _
    _ <= ∑ n ∈ active, Real.log ((u + 1 : Nat) : Real) :=
      Finset.sum_le_sum hterm
    _ = (active.card : Real) * Real.log ((u + 1 : Nat) : Real) := by simp
    _ <= (u : Real) * Real.log ((u + 1 : Nat) : Real) := by
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg (u + 1))
      have hcard : active.card <= u := by
        calc
          active.card <= (Icc 1 u).card := Finset.card_le_card hactive
          _ = u := by simp
      exact_mod_cast hcard

def maximalVaughanS4Norm (u X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖

theorem maximalVaughanS4Norm_le (u X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalVaughanS4Norm u X q chi <=
      (u : Real) * Real.log ((u + 1 : Nat) : Real) := by
  unfold maximalVaughanS4Norm
  apply Finset.sup'_le
  intro Y hY
  exact norm_vaughanS4_le u Y q chi

def vaughanS4Mean (u X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalVaughanS4Norm u X q chi

theorem vaughanS4Mean_le (u X Q : Nat) :
    vaughanS4Mean u X Q <=
      (u : Real) * (Q : Real) ^ 2 * Real.log ((u + 1 : Nat) : Real) := by
  let B : Real := (u : Real) * Real.log ((u + 1 : Nat) : Real)
  have hB : 0 <= B := by dsimp [B]; positivity
  unfold vaughanS4Mean
  calc
    _ <= ∑ q ∈ Icc 1 Q, (q : Real) * B := by
      apply Finset.sum_le_sum
      intro q hq
      let _ : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      have hchars : ∑ chi ∈ primitiveCharacters q, maximalVaughanS4Norm u X q chi <=
          (q.totient : Real) * B := by
        calc
          _ <= ∑ chi ∈ primitiveCharacters q, B := by
            apply Finset.sum_le_sum
            intro chi hchi
            exact maximalVaughanS4Norm_le u X q chi
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
    _ <= ∑ q ∈ Icc 1 Q, (Q : Real) * B := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (Finset.mem_Icc.mp hq).2
    _ = (Q : Real) ^ 2 * B := by simp; ring
    _ = _ := by dsimp [B]; ring

end BombieriVinogradov.VaughanMeanValue
