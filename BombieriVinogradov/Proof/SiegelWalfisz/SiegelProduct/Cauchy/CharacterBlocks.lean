import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.AnalyticDomain
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Zero-sum character L-function blocks

This module owns the grouped Dirichlet blocks, their zero-sum recentering, and
their termwise holomorphy on the fixed analytic domain.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- One complete residue block of the Dirichlet series of a character. -/
noncomputable def characterLBlock {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)

theorem characterLBlock_recenter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (s : ℂ) :
    characterLBlock χ k s =
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) := by
  rw [characterLBlock]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [χ.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem characterLBlock_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) :
    DifferentiableOn ℂ (characterLBlock χ k) siegelAnalyticDomain := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [show characterLBlock χ k = fun s ↦
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) by
    funext s
    exact characterLBlock_recenter χ hχ k s]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [χ.map_zero' hN]
    simp
  · have hx : ((k * N + j.val : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (by
        have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        omega)
    have hy : ((((k + 1) * N : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (NeZero.ne N))
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hy))).const_mul (χ j)

end BombieriVinogradov.SiegelWalfisz
