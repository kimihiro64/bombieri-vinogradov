import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.CharacterFacts
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueReality
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ZetaSign
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Value

/-!
# Real-part normalization for the four-factor Siegel product

This module isolates the complex-algebra step that turns the real part of the
Siegel product into the product of four real parts for quadratic characters.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_eq_product {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : Ne chi 1) (hpsi : Ne psi 1)
    (hmul : Ne (DirichletCharacter.mul chi psi) 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1) :
    (siegelProductValue chi psi s).re =
      (riemannZeta s).re * (chi.LFunction s).re * (psi.LFunction s).re *
        ((DirichletCharacter.mul chi psi).LFunction s).re := by
  have hmulSquare := crossLevelMul_sq_eq_one chi psi hchiSquare hpsiSquare
  have hzetaIm := riemannZeta_im_real s
  have hchiIm := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hpsiIm := quadraticLFunction_im_eq_zero psi hpsiSquare hpsi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hmulIm := quadraticLFunction_im_eq_zero (DirichletCharacter.mul chi psi)
    hmulSquare hmul (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  simp only [siegelProductValue, siegelLProduct, Complex.mul_re, Complex.mul_im,
    hzetaIm, hchiIm, hpsiIm, hmulIm, mul_zero, zero_mul, add_zero, sub_zero]
  ring

end BombieriVinogradov.SiegelWalfisz
