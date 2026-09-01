import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Decomposition

/-!
# Quantitative lower bound before cutoff selection

This module converts the exact decomposition and norm tail estimate into a real lower bound.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_lower_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {A delta : ℝ} (hA : 0 ≤ A) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    {cutoff : ℕ} (hcutoff : 0 < cutoff)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    1 - (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta -
        4 * A * (3 / 4 : ℝ) ^ cutoff ≤
      (siegelProductValue chi psi (1 - delta)).re := by
  let partialSum := siegelSourcePartialSum chi psi cutoff (1 + delta)
  let tail := regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta)
  have hpartialComplex : (1 : ℂ) ≤ partialSum :=
    one_le_siegelSourcePartialSum chi psi hchiSquare hpsiSquare hcutoff (by linarith)
  have hpartial : 1 ≤ partialSum.re := (Complex.le_def.mp hpartialComplex).1
  have htailNorm : ‖tail‖ ≤ 4 * A * (3 / 4 : ℝ) ^ cutoff :=
    norm_regularCoefficientTail_le (siegelRegularCoefficient chi psi) cutoff hA
      (by linarith) (by linarith) hcoeff
  have htailRe : -(4 * A * (3 / 4 : ℝ) ^ cutoff) ≤ tail.re := by
    exact (neg_le_neg htailNorm).trans ((abs_le.mp (Complex.abs_re_le_norm tail)).1)
  have hdecomp := congrArg Complex.re
    (siegelProductValue_decomposition chi psi hchi hpsi hmul cutoff hdelta)
  have hpowcast : (((1 + delta : ℝ) : ℂ) ^ cutoff) =
      (((1 + delta) ^ cutoff : ℝ) : ℂ) := by
    norm_cast
  have hbasecast : (1 : ℂ) + delta = ((1 + delta : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpowRe : ((1 + (delta : ℂ)) ^ cutoff).re = (1 + delta) ^ cutoff := by
    rw [hbasecast, hpowcast]
    rfl
  have hpowIm : ((1 + (delta : ℂ)) ^ cutoff).im = 0 := by
    rw [hbasecast, hpowcast]
    rfl
  have hpoleRe :
      (siegelProductResidue chi psi * (((1 + delta : ℝ) : ℂ) ^ cutoff) / delta).re =
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta := by
    simp
    rw [hpowRe, hpowIm]
    ring
  rw [Complex.sub_re, Complex.add_re, hpoleRe] at hdecomp
  change (siegelProductValue chi psi (1 - delta)).re =
      partialSum.re + tail.re -
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta at hdecomp
  linarith

end BombieriVinogradov.SiegelWalfisz
