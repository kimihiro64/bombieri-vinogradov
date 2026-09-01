import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFunctionalEquation

/-!
# Reflection of zeros of completed Dirichlet L-functions

This module extracts the value-level zero symmetry `rho ↔ 1 - rho` between a
primitive character and its inverse from the symmetric functional equation.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_eq_zero_iff_inv_one_sub
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : DirichletCharacter.IsPrimitive chi) (rho : ℂ) :
    symmetricCompletedLFunction chi rho = 0 ↔
      symmetricCompletedLFunction chi⁻¹ (1 - rho) = 0 := by
  have hinv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv, hchi]
  constructor
  · intro hzero
    simpa [hzero] using
      (symmetricCompletedLFunction_one_sub hinv rho)
  · intro hzero
    simpa [hzero] using
      (symmetricCompletedLFunction_one_sub hchi (1 - rho))

end BombieriVinogradov.SiegelWalfisz
