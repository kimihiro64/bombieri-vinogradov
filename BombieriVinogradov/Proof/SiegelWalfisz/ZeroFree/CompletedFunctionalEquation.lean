import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization

/-!
# Functional equation of the symmetric completed L-function

This module derives the primitive functional equation for the symmetric
normalization, with no residual modulus power.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_one_sub {N : ℕ} [NeZero N]
    {chi : DirichletCharacter ℂ N} (hchi : DirichletCharacter.IsPrimitive chi)
    (s : ℂ) :
    symmetricCompletedLFunction chi (1 - s) =
      chi.rootNumber * symmetricCompletedLFunction chi⁻¹ s := by
  have hN : Ne (N : ℂ) 0 := by exact_mod_cast NeZero.ne N
  have hpower :
      (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) =
        (N : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_add _ _ hN]
    congr 1
    ring
  rw [symmetricCompletedLFunction,
    hchi.completedLFunction_one_sub]
  change (N : ℂ) ^ ((1 - s) / 2) *
      ((N : ℂ) ^ (s - 1 / 2) * chi.rootNumber *
        chi⁻¹.completedLFunction s) =
    chi.rootNumber *
      ((N : ℂ) ^ (s / 2) * chi⁻¹.completedLFunction s)
  calc
    (N : ℂ) ^ ((1 - s) / 2) *
        ((N : ℂ) ^ (s - 1 / 2) * chi.rootNumber *
          chi⁻¹.completedLFunction s) =
      ((N : ℂ) ^ ((1 - s) / 2) *
        (N : ℂ) ^ (s - 1 / 2)) * chi.rootNumber *
          chi⁻¹.completedLFunction s := by ring
    _ = (N : ℂ) ^ (s / 2) * chi.rootNumber *
          chi⁻¹.completedLFunction s := by rw [hpower]
    _ = chi.rootNumber *
        ((N : ℂ) ^ (s / 2) * chi⁻¹.completedLFunction s) := by ring

end BombieriVinogradov.SiegelWalfisz
