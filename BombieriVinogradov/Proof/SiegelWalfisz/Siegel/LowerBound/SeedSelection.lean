import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.SeedPoint
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.SeedProductSign

/-!
# Source dichotomy selecting a fixed Siegel seed

This module assembles the two cases in Strombergsson's proof: either one
primitive quadratic L-function vanishes near one, or the fixed character
modulo four gives a nonpositive four-factor product at a zeta-negative point.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- A fixed character and comparison point that work for every larger target level. -/
def IsSiegelSeed (lower : ℝ) (N : ℕ) (chi : DirichletCharacter ℂ N)
    (s : ℝ) : Prop :=
  0 < N ∧ DirichletCharacter.IsPrimitive chi ∧ chi ^ 2 = 1 ∧ Ne chi 1 ∧
    lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧
      ∀ (M : ℕ) [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (psi : DirichletCharacter ℂ M), N < M ->
          DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
            (siegelProductValue chi psi s).re ≤ 0

theorem exists_siegelSeed {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ (N : ℕ) (chi : DirichletCharacter ℂ N) (s : ℝ),
      IsSiegelSeed lower N chi s := by
  by_cases hzeroFree : PrimitiveQuadraticZeroFreeFrom lower
  · obtain ⟨s, hlowerS, hsevenS, hsUpper, hzeta⟩ :=
      exists_siegelComparisonPoint hlower hupper
    have hzeroFreeS := hzeroFree.mono hlowerS
    refine ⟨4, quadraticCharacterFour, s, ?_⟩
    refine ⟨by norm_num, quadraticCharacterFour_isPrimitive,
      quadraticCharacterFour_sq, quadraticCharacterFour_ne_one,
      hlowerS, hsevenS, hsUpper, ?_⟩
    intro M _ _ _ psi hM hpsiPrimitive hpsiSquare hpsi
    exact quadraticCharacterFour_product_nonpos_of_zeroFree psi hpsiPrimitive
      hpsiSquare hpsi hM hsevenS hsUpper hzeta hzeroFreeS
  · rw [PrimitiveQuadraticZeroFreeFrom] at hzeroFree
    push Not at hzeroFree
    obtain ⟨N, hN, chi, hprimitive, hchiSquare, hchi, s,
      hlowerS, hsOne, hzero⟩ := hzeroFree
    let _ : NeZero N := hN
    have hsUpper : s < 1 := by
      apply lt_of_le_of_ne hsOne
      intro hs
      apply chi.LFunction_apply_one_ne_zero hchi
      simpa [hs] using hzero
    refine ⟨N, chi, s, ?_⟩
    refine ⟨NeZero.pos N, hprimitive, hchiSquare, hchi,
      hlowerS, hlower.trans hlowerS, hsUpper, ?_⟩
    intro M _ _ _ psi _ _ _ _
    exact siegelProductValue_nonpos_of_left_zero chi psi hzero

end BombieriVinogradov.SiegelWalfisz
