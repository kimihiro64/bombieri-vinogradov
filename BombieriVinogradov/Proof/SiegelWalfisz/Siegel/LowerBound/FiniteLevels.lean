import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValuePositivity
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# The finite small-level remainder in Siegel's lower bound

This module takes a positive minimum over all quadratic nonprincipal character
values at levels bounded by a fixed seed level.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

abbrev BoundedDirichletCharacter (N : ℕ) :=
  Σ M : Fin (N + 1), DirichletCharacter ℂ M.val

noncomputable def finiteLevelValue (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) : ℝ := by
  classical
  exact if hlevel : 0 < entry.1.val then
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      if hquadratic : entry.2 ^ 2 = 1 ∧ Ne entry.2 1 then
        (entry.2.LFunction 1).re * (entry.1.val : ℝ) ^ epsilon
      else
        1
    else
      1

theorem finiteLevelValue_pos (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) :
    0 < finiteLevelValue epsilon entry := by
  classical
  rw [finiteLevelValue]
  split
  · next hlevel =>
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      split
      · next hquadratic =>
          have hlevelReal : (0 : ℝ) < (entry.1.val : ℕ) := by
            exact_mod_cast hlevel
          exact mul_pos
            (quadraticLFunction_one_re_pos entry.2 hquadratic.1 hquadratic.2)
            (Real.rpow_pos_of_pos hlevelReal epsilon)
      · norm_num
  · norm_num

noncomputable def finiteLevelValues (epsilon : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset (BoundedDirichletCharacter N)).image
    (finiteLevelValue epsilon)

theorem finiteLevelValues_nonempty (epsilon : ℝ) (N : ℕ) :
    (finiteLevelValues epsilon N).Nonempty := by
  classical
  unfold finiteLevelValues
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

noncomputable def finiteLevelConstant (epsilon : ℝ) (N : ℕ) : ℝ :=
  (finiteLevelValues epsilon N).min' (finiteLevelValues_nonempty epsilon N)

theorem finiteLevelConstant_pos (epsilon : ℝ) (N : ℕ) :
    0 < finiteLevelConstant epsilon N := by
  classical
  have hmem := Finset.min'_mem (finiteLevelValues epsilon N)
    (finiteLevelValues_nonempty epsilon N)
  unfold finiteLevelValues at hmem
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp hmem
  unfold finiteLevelConstant
  unfold finiteLevelValues
  rw [← hentry]
  exact finiteLevelValue_pos epsilon entry

theorem finiteLevelConstant_le_value {epsilon : ℝ} {N M : ℕ}
    [NeZero M] (hMN : M ≤ N) (hM : 3 ≤ M)
    (psi : DirichletCharacter ℂ M) (hpsiSquare : psi ^ 2 = 1)
    (hpsi : Ne psi 1) :
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
      (psi.LFunction 1).re := by
  classical
  let level : Fin (N + 1) := ⟨M, Nat.lt_succ_of_le hMN⟩
  let entry : BoundedDirichletCharacter N := ⟨level, psi⟩
  have hlevel : 0 < level.val := by
    dsimp [level]
    omega
  have hentryValue : finiteLevelValue epsilon entry =
      (psi.LFunction 1).re * (M : ℝ) ^ epsilon := by
    rw [finiteLevelValue]
    simp [entry, level, hlevel, hpsiSquare, hpsi]
  have hentryMem : finiteLevelValue epsilon entry ∈ finiteLevelValues epsilon N := by
    rw [finiteLevelValues]
    exact Finset.mem_image.mpr ⟨entry, Finset.mem_univ _, rfl⟩
  have hminimum : finiteLevelConstant epsilon N ≤ finiteLevelValue epsilon entry := by
    exact Finset.min'_le _ _ hentryMem
  rw [hentryValue] at hminimum
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hscaled := mul_le_mul_of_nonneg_right hminimum
    (Real.rpow_nonneg hMnonneg (-epsilon))
  calc
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
        ((psi.LFunction 1).re * (M : ℝ) ^ epsilon) *
          (M : ℝ) ^ (-epsilon) := hscaled
    _ = (psi.LFunction 1).re := by
      rw [mul_assoc, ← Real.rpow_add hMpos]
      norm_num

end BombieriVinogradov.SiegelWalfisz
