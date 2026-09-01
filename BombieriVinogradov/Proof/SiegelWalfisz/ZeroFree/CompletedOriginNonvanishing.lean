import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveRootNumberNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFunctionalEquation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Nonvanishing of completed Dirichlet L-functions at the origin

This module proves nonvanishing at one for a nonprincipal character and transfers it to
the origin for a primitive character through the symmetric functional equation.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_one_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) :
    symmetricCompletedLFunction chi 1 ≠ 0 := by
  have hNNeOne : N ≠ 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hGammaNe : chi.gammaFactor 1 ≠ 0 := by
    rcases chi.even_or_odd with hEven | hOdd
    · rw [hEven.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
    · rw [hOdd.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hCompleted : chi.completedLFunction 1 =
      chi.LFunction 1 * chi.gammaFactor 1 := by
    exact ((eq_div_iff hGammaNe).mp
      (chi.LFunction_eq_completed_div_gammaFactor 1 (.inr hNNeOne))).symm
  have hLFunction : chi.LFunction 1 ≠ 0 :=
    chi.LFunction_ne_zero_of_one_le_re (.inl hchi) (by norm_num)
  rw [symmetricCompletedLFunction, hCompleted]
  apply mul_ne_zero
  · have hNCast : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
    exact Complex.cpow_ne_zero_iff.mpr (.inl hNCast)
  · exact mul_ne_zero hLFunction hGammaNe

theorem symmetricCompletedLFunction_zero_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    symmetricCompletedLFunction chi 0 ≠ 0 := by
  have hInverseNe : chi⁻¹ ≠ 1 := by
    intro hInverse
    apply hchi
    calc
      chi = (chi⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter Complex N)⁻¹ := congrArg Inv.inv hInverse
      _ = 1 := by simp
  have hFunctional :
      symmetricCompletedLFunction chi 0 =
        chi.rootNumber * symmetricCompletedLFunction chi⁻¹ 1 := by
    simpa using symmetricCompletedLFunction_one_sub hPrimitive (1 : Complex)
  rw [hFunctional]
  exact mul_ne_zero (BombieriVinogradov.primitive_rootNumber_ne_zero hPrimitive)
    (symmetricCompletedLFunction_one_ne_zero hInverseNe)

end BombieriVinogradov.SiegelWalfisz
