import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Symmetric normalization of a completed Dirichlet L-function

This module defines the completed L-function normalization whose functional
equation is symmetric about `re s = 1 / 2`, and proves that it is entire for a
nonprincipal character.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def symmetricCompletedLFunction {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * chi.completedLFunction s

theorem differentiable_symmetricCompletedLFunction {N : ℕ} [NeZero N]
    {chi : DirichletCharacter ℂ N} (hchi : Ne chi 1) :
    Differentiable ℂ (symmetricCompletedLFunction chi) := by
  have hN : Ne (N : ℂ) 0 := by exact_mod_cast NeZero.ne N
  have hpower : Differentiable ℂ (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) :=
    (differentiable_id.div_const 2).const_cpow (.inl hN)
  exact hpower.mul (chi.differentiable_completedLFunction hchi)

end BombieriVinogradov.SiegelWalfisz
