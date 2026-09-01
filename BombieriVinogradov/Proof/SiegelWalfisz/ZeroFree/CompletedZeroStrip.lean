import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFunctionalEquation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroDivisorValues
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The critical strip for completed-function divisor zeros

This module proves right-half-plane nonvanishing and uses the reflected zero symmetry
to place every divisor-indexed zero strictly between real parts zero and one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_ne_zero_of_one_le_re
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) {s : Complex} (hs : 1 <= s.re) :
    symmetricCompletedLFunction chi s ≠ 0 := by
  have hsPos : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  have hNCast : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hPower : (N : Complex) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl hNCast)
  have hLFunction : chi.LFunction s ≠ 0 :=
    chi.LFunction_ne_zero_of_one_le_re (.inl hchi) hs
  have hGamma : chi.gammaFactor s ≠ 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hsPos
  rw [symmetricCompletedLFunction,
    DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
      chi hsPos]
  exact mul_ne_zero hPower (mul_ne_zero hLFunction hGamma)

theorem symmetricCompletedLFunction_one_sub_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (s : Complex) :
    symmetricCompletedLFunction chi (1 - (starRingEnd Complex) s) =
      chi.rootNumber *
        (starRingEnd Complex) (symmetricCompletedLFunction chi s) := by
  rw [symmetricCompletedLFunction_one_sub hPrimitive]
  rw [symmetricCompletedLFunction_inv_eq_conj_conj hchi]
  simp only [Complex.conj_conj]

theorem symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    (Complex.Hadamard.divisorZeroIndex₀_val p).re ∈ Set.Ioo 0 1 := by
  let rho := Complex.Hadamard.divisorZeroIndex₀_val p
  have hZero : symmetricCompletedLFunction chi rho = 0 :=
    symmetricCompletedLFunction_divisorZeroIndex₀_apply_eq_zero
      hchi hPrimitive p
  have hUpper : rho.re < 1 := by
    by_contra hNot
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re
      hchi (le_of_not_gt hNot) hZero
  have hLower : 0 < rho.re := by
    by_contra hNot
    have hReflectedRe : 1 <= (1 - (starRingEnd Complex) rho).re := by
      have hConjRe : ((starRingEnd Complex) rho).re = rho.re := by simp
      rw [Complex.sub_re, hConjRe]
      norm_num
      linarith
    have hReflectedZero :
        symmetricCompletedLFunction chi (1 - (starRingEnd Complex) rho) = 0 := by
      rw [symmetricCompletedLFunction_one_sub_conj hchi hPrimitive, hZero,
        map_zero, mul_zero]
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re
      hchi hReflectedRe hReflectedZero
  exact Set.mem_Ioo.mpr (And.intro hLower hUpper)

end BombieriVinogradov.SiegelWalfisz
