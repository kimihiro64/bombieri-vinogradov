import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LevelCorrection
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ZeroFreeSign

/-!
# Zero-free positivity transferred from the primitive character

This module combines primitive-character positivity with the positive finite
Euler correction for an imprimitive quadratic character.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_primitive_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 →
      chi.primitiveCharacter.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  have hprimitiveNe := primitiveCharacter_ne_one chi hchi
  have hprimitiveSquare := primitiveCharacter_sq_eq_one chi hchiSquare
  have hprimitivePos := quadraticLFunction_re_pos_of_no_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe hsLower hsUpper hnozero
  have hcorrection := characterLevelCorrection_pos chi hchiSquare
    (show 0 < s by linarith)
  have hcorrectionParts := Complex.lt_def.mp hcorrection
  have hprimitiveIm := quadraticLFunction_im_eq_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  rw [LFunction_eq_primitive_mul_correction chi hchi, Complex.mul_re]
  rw [hprimitiveIm]
  norm_num
  exact mul_pos hprimitivePos (by simpa using hcorrectionParts.1)

end BombieriVinogradov.SiegelWalfisz
