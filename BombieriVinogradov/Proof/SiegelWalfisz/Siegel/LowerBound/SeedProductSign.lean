import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.PrimitiveTransfer
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ProductReality
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.ZeroFreeFamily

/-!
# Sign of the source's seeded four-factor product

This module proves the product is nonpositive either because its seed
L-function vanishes or because zeta is negative while all three quadratic
L-functions are positive.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_nonpos_of_left_zero {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℝ} (hzero : chi.LFunction s = 0) :
    (siegelProductValue chi psi s).re ≤ 0 := by
  simp [siegelProductValue, siegelLProduct, hzero]

theorem quadraticCharacterFour_product_nonpos_of_zeroFree {M : ℕ}
    [NeZero M] [NeZero ((4 : ℕ).lcm M)]
    (psi : DirichletCharacter ℂ M)
    (hpsiPrimitive : DirichletCharacter.IsPrimitive psi)
    (hpsiSquare : psi ^ 2 = 1) (hpsi : Ne psi 1)
    (hM : 4 < M) {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hzeta : (riemannZeta s).re < 0)
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom s) :
    (siegelProductValue quadraticCharacterFour psi s).re ≤ 0 := by
  have hlevels : Ne 4 M := Ne.symm (Nat.ne_of_gt hM)
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne quadraticCharacterFour psi
    quadraticCharacterFour_isPrimitive hpsiPrimitive hlevels
  have hmulSquare := crossLevelMul_sq_eq_one quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare
  have hfourNoZero := hzeroFree 4 quadraticCharacterFour
    quadraticCharacterFour_isPrimitive quadraticCharacterFour_sq
      quadraticCharacterFour_ne_one
  have hfourPos := quadraticLFunction_re_pos_of_no_zero quadraticCharacterFour
    quadraticCharacterFour_sq quadraticCharacterFour_ne_one hsLower hsUpper hfourNoZero
  have hpsiNoZero := hzeroFree M psi hpsiPrimitive hpsiSquare hpsi
  have hpsiPos := quadraticLFunction_re_pos_of_no_zero psi hpsiSquare hpsi
    hsLower hsUpper hpsiNoZero
  let _ : NeZero (DirichletCharacter.mul quadraticCharacterFour psi).conductor :=
    ⟨(DirichletCharacter.mul quadraticCharacterFour psi).conductor_ne_zero⟩
  have hmulPrimitiveSquare := primitiveCharacter_sq_eq_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare
  have hmulPrimitiveNe := primitiveCharacter_ne_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmul
  have hmulPrimitiveNoZero := hzeroFree
    (DirichletCharacter.mul quadraticCharacterFour psi).conductor
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter_isPrimitive
    hmulPrimitiveSquare hmulPrimitiveNe
  have hmulPos := quadraticLFunction_re_pos_of_primitive_no_zero
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare hmul
      hsLower hsUpper hmulPrimitiveNoZero
  rw [siegelProductValue_re_eq_product quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare quadraticCharacterFour_ne_one hpsi hmul
      hsLower hsUpper]
  exact (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hzeta hfourPos) hpsiPos)
      hmulPos).le

end BombieriVinogradov.SiegelWalfisz
