import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.LowerBound
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Residue
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Truncation.Main

/-!
# Positivity criterion from a uniform coefficient bound

This module combines the quantitative lower bound with the two cutoff estimates.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos_of_coefficient_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {C B Q delta : ℝ} {K : ℕ}
    (hC : 0 < C) (hB : 1 ≤ B) (hCB : 8 * C ≤ B) (hQ : 1 ≤ Q)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤
      C * Q ^ K * (2 / 3 : ℝ) ^ m)
    (hsmall : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
      Q ^ ((4 * K : ℝ) * delta) < delta) :
    0 < (siegelProductValue chi psi (1 - delta)).re := by
  let cutoff := siegelTruncationIndex B Q K
  have hcutoff : 0 < cutoff := by
    dsimp [cutoff, siegelTruncationIndex]
    omega
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueRe : 0 ≤ (siegelProductResidue chi psi).re :=
    (Complex.le_def.mp hresidue).1
  have htruncation := siegelTruncation_spec (K := K)
    hC.le hB hCB hQ hdelta.le hdeltaUpper
  have htail : 4 * (C * Q ^ K) * (3 / 4 : ℝ) ^ cutoff < 1 / 2 := by
    simpa only [mul_assoc] using htruncation.1
  have hpoleGrowth : (1 + delta) ^ cutoff ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := htruncation.2
  have hpoleNumerator :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff ≤
        (siegelProductResidue chi psi).re *
          (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) :=
    mul_le_mul_of_nonneg_left hpoleGrowth hresidueRe
  have hpole :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta < 1 / 2 := by
    calc
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta ≤
          (siegelProductResidue chi psi).re *
            (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) / delta :=
        div_le_div_of_nonneg_right hpoleNumerator hdelta.le
      _ < 1 / 2 := by
        rw [div_lt_iff₀ hdelta]
        ring_nf at hsmall ⊢
        linarith
  have hlower := siegelProductValue_re_lower_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul (mul_nonneg hC.le (pow_nonneg (zero_le_one.trans hQ) K))
    hdelta hdeltaUpper hcutoff hcoeff
  linarith

end BombieriVinogradov.SiegelWalfisz
