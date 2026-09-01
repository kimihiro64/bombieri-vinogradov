import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.FiniteLevels
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LargeLevel
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.PositivityData
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.SeedSelection

/-!
# Siegel's non-effective lower bound

This module only assembles the large-level estimate and the positive minimum
over the finite small-level remainder.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- Strombergsson's Theorem 16.1 in the form needed for Siegel--Walfisz. -/
theorem siegelLowerBound :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ (M : ℕ) [NeZero M] (psi : DirichletCharacter ℂ M), 3 ≤ M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          c * (M : ℝ) ^ (-epsilon) ≤ (psi.LFunction 1).re := by
  intro epsilon hepsilon
  obtain ⟨C, D, hpair⟩ := exists_siegelPositivityPair
  obtain ⟨N, chi, s, hseed⟩ := exists_siegelSeed
    (seven_eighths_le_siegelLowerEndpoint epsilon D)
    (siegelLowerEndpoint_lt_one hepsilon D)
  have hN : 0 < N := hseed.1
  have hsUpper : s < 1 := hseed.2.2.2.2.2.2.1
  let _ : NeZero N := ⟨hN.ne'⟩
  let c := min (finiteLevelConstant epsilon N)
    (siegelLargeLevelConstant C epsilon s N)
  have hcPositive : 0 < c := by
    apply lt_min
    · exact finiteLevelConstant_pos epsilon N
    · exact siegelLargeLevelConstant_pos hpair.1 hepsilon hN hsUpper
  refine ⟨c, hcPositive, ?_⟩
  intro M _ psi hM hpsiPrimitive hpsiSquare hpsi
  have hpowerNonneg : 0 ≤ (M : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg M) (-epsilon)
  by_cases hMN : M ≤ N
  · have hcoefficient : c ≤ finiteLevelConstant epsilon N := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (finiteLevelConstant_le_value hMN hM psi hpsiSquare hpsi)
  · have hNM : N < M := Nat.lt_of_not_ge hMN
    let _ : NeZero (N.lcm M) :=
      ⟨Nat.lcm_ne_zero hN.ne' (NeZero.ne M)⟩
    have hcoefficient : c ≤ siegelLargeLevelConstant C epsilon s N :=
      min_le_right _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (siegelLowerBound_largeLevel hpair hepsilon hseed M psi hNM
        hpsiPrimitive hpsiSquare hpsi)

end BombieriVinogradov.SiegelWalfisz
