import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Coefficients

/-!
# Cross-level products of Dirichlet characters

This module proves that Mathlib's common-level product agrees with pointwise multiplication on naturals.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem crossLevelMul_apply_nat {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    DirichletCharacter.mul χ ψ n = χ n * ψ n := by
  rw [DirichletCharacter.mul, MulChar.mul_apply]
  by_cases hN : n.Coprime N
  · by_cases hM : n.Coprime M
    · have hLcm : n.Coprime (N.lcm M) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul N M) (hN.mul_right hM)
      have hLcmInt : IsCoprime (n : ℤ) (N.lcm M) :=
        Nat.isCoprime_iff_coprime.mpr hLcm
      have hχEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = χ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' χ _ hLcmInt
      have hψEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = ψ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ _ hLcmInt
      rw [hχEval, hψEval]
    · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
        hM (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right N M) h)
      have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
        hLcm (Nat.isCoprime_iff_coprime.mp h)
      have hMInt : ¬IsCoprime (n : ℤ) M := fun h ↦
        hM (Nat.isCoprime_iff_coprime.mp h)
      have hLiftZero :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
      have hZero : ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hMInt
      rw [hLiftZero, hZero, mul_zero, mul_zero]
  · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
      hN (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left N M) h)
    have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
      hLcm (Nat.isCoprime_iff_coprime.mp h)
    have hNInt : ¬IsCoprime (n : ℤ) N := fun h ↦
      hN (Nat.isCoprime_iff_coprime.mp h)
    have hLiftZero :
        DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
    have hZero : χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hNInt
    rw [hLiftZero, hZero, zero_mul, zero_mul]

end BombieriVinogradov.SiegelWalfisz
