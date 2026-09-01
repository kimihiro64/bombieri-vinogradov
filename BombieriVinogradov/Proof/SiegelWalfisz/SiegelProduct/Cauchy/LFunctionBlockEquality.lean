import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlockSeries

/-!
# Identification of the grouped character series

This module identifies the locally uniformly convergent residue-block series
with Mathlib's analytically continued Dirichlet L-function.
-/

set_option autoImplicit false

open Complex Filter LSeries Metric Set Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_characterLBlockSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = characterLBlockSeries χ s := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  have hzero : (fun n : ℕ ↦ χ n) 0 = 0 := by
    simpa using χ.map_zero' hN
  have hsum : Summable (fun n : ℕ ↦ χ n * (n : ℂ) ^ (-s)) := by
    rw [← funext (LSeries.term_def₀ hzero s)]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hterm (j : ZMod N) (k : ℕ) :
      χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) =
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
    have hcast : ((j.val + N * k : ℕ) : ZMod N) = j := by
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    congr 2
    simp only [Nat.add_comm, Nat.mul_comm]
  have hsub (j : ZMod N) :
      Summable (fun k : ℕ ↦ χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ j.val + N * k) := by
      intro a b hab
      exact Nat.mul_left_cancel (NeZero.pos N) (Nat.add_left_cancel hab)
    have h := hsum.comp_injective hinj
    exact h.congr (hterm j)
  have hswap := Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _hj ↦ hsub j)
  calc
    χ.LFunction s = LSeries (χ ·) s := DirichletCharacter.LFunction_eq_LSeries χ hs
    _ = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
      rw [LSeries_def₀ hzero]
      congr 1
      funext n
      rw [Complex.cpow_neg, div_eq_mul_inv]
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) :=
      Nat.sumByResidueClasses hsum N
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_congr (hterm j)
    _ = ∑' k : ℕ, ∑ j : ZMod N,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      simpa only [Finset.mem_univ, ↓reduceIte] using hswap.symm
    _ = characterLBlockSeries χ s := rfl

theorem LFunction_eq_characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) : χ.LFunction s = characterLBlockSeries χ s := by
  have hL : AnalyticOnNhd ℂ (χ.LFunction) siegelAnalyticDomain :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hB : AnalyticOnNhd ℂ (characterLBlockSeries χ) siegelAnalyticDomain :=
    (characterLBlockSeries_differentiableOn χ hχ).analyticOnNhd Metric.isOpen_ball
  have h2 : (2 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)] characterLBlockSeries χ := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    exact LFunction_eq_characterLBlockSeries_of_one_lt_re χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_ball (2 : ℂ) (7 / 4 : ℝ)).isPreconnected h2 heq hs

end BombieriVinogradov.SiegelWalfisz
