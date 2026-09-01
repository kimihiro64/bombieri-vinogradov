import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.CharacterFacts
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LevelCorrection
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.PrimitiveCase

/-!
# Transfer of zero exclusion from the primitive character

This module transfers primitive quadratic nonvanishing to every nonprincipal
quadratic character through the finite Euler correction.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem nonprincipalQuadratic_zeroExclusion_of_primitive
    {epsilon c : ℝ} (hepsilon : 0 < epsilon) (hcPos : 0 < c)
    (hcSmall : c ≤ 1 / 16)
    (hprimitive :
      ∀ (M : ℕ) [NeZero M] (psi : DirichletCharacter ℂ M), 3 ≤ M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          ∀ t : ℝ, 1 - c * (M : ℝ) ^ (-epsilon) < t ->
            Ne (psi.LFunction t) 0) :
    ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
      chi ^ 2 = 1 -> Ne chi 1 -> ∀ t : ℝ,
        1 - c * (N : ℝ) ^ (-epsilon) < t ->
          Ne (chi.LFunction t) 0 := by
  intro N _ chi hchiSquare hchi t ht
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hpowerNonneg : 0 ≤ (N : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg hNpos.le _
  have hpowerLeOne : (N : ℝ) ^ (-epsilon) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNreal (by linarith)
  have hwidthSmall : c * (N : ℝ) ^ (-epsilon) ≤ 1 / 16 := by
    calc
      c * (N : ℝ) ^ (-epsilon) ≤
          (1 / 16 : ℝ) * (N : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_right hcSmall hpowerNonneg
      _ ≤ (1 / 16 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hpowerLeOne (by norm_num)
      _ = 1 / 16 := mul_one _
  have htPos : 0 < t := by linarith
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hconductorLe : chi.conductor ≤ N :=
    Nat.le_of_dvd (NeZero.pos N) chi.conductor_dvd_level
  have hconductorPos : (0 : ℝ) < chi.conductor := by
    exact_mod_cast NeZero.pos chi.conductor
  have hconductorLeReal : (chi.conductor : ℝ) ≤ N := by
    exact_mod_cast hconductorLe
  have hpowerCompare :
      (N : ℝ) ^ (-epsilon) ≤ (chi.conductor : ℝ) ^ (-epsilon) :=
    Real.rpow_le_rpow_of_nonpos hconductorPos hconductorLeReal (by linarith)
  have hscaledCompare :
      c * (N : ℝ) ^ (-epsilon) ≤
        c * (chi.conductor : ℝ) ^ (-epsilon) :=
    mul_le_mul_of_nonneg_left hpowerCompare hcPos.le
  have hprimitiveValue : Ne (chi.primitiveCharacter.LFunction t) 0 := by
    apply hprimitive chi.conductor chi.primitiveCharacter
      (three_le_conductor_of_ne_one chi hchi)
      chi.primitiveCharacter_isPrimitive
      (primitiveCharacter_sq_eq_one chi hchiSquare)
      (primitiveCharacter_ne_one chi hchi)
      t
    linarith
  have hcorrection : Ne (characterLevelCorrection chi t) 0 :=
    ne_of_gt (characterLevelCorrection_pos chi hchiSquare htPos)
  rw [LFunction_eq_primitive_mul_correction chi hchi]
  exact mul_ne_zero hprimitiveValue hcorrection

end BombieriVinogradov.SiegelWalfisz
