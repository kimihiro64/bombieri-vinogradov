import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveEmptyZeroLogDerivativeBound

/-!
# Nonprincipal logarithmic-derivative bound

The primitive empty-zero estimate is transferred to an arbitrary nonprincipal
character using the finite level-correction bound.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_nonprincipal_logDeriv_bound :
    exists A : Real, 0 < A ∧
      forall {N : Nat} [NeZero N]
        {chi : DirichletCharacter Complex N}, chi ≠ 1 ->
          forall {s : Complex}, 1 < s.re -> s.re ≤ 2 ->
            -(logDeriv chi.LFunction s).re ≤
              A * (Real.log N + Real.log (|s.im| + 2)) := by
  obtain ⟨A, hAPos, hPrimitive⟩ := exists_primitive_logDeriv_bound
  refine Exists.intro (A + 1) (And.intro (add_pos hAPos zero_lt_one) ?_)
  intro N _hN chi hchi s hsLower hsUpper
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hPrimitiveNe :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi
  have hConductorLower :=
    BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hchi
  have hPrimitiveBound := hPrimitive hConductorLower hPrimitiveNe
    chi.primitiveCharacter_isPrimitive hsLower hsUpper
  have hCorrection := norm_logDeriv_LFunction_sub_primitive_le_log
    chi hchi hsLower.le
  have hConductorLe :=
    BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hLogConductorLe : Real.log chi.conductor ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (NeZero.pos chi.conductor))
      (by exact_mod_cast hConductorLe)
  have hLogNNonneg : 0 ≤ Real.log N := by
    apply Real.log_nonneg
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3)
      (BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi))
  have hLogHeightNonneg : 0 ≤ Real.log (|s.im| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg s.im]
  have hPrimitiveAmbient :
      -(logDeriv chi.primitiveCharacter.LFunction s).re ≤
        A * (Real.log N + Real.log (|s.im| + 2)) :=
    hPrimitiveBound.trans (mul_le_mul_of_nonneg_left
      (add_le_add hLogConductorLe le_rfl) hAPos.le)
  have hDifferenceReal :
      -(logDeriv chi.LFunction s).re ≤
        -(logDeriv chi.primitiveCharacter.LFunction s).re + Real.log N := by
    have hRealNorm :
        -(logDeriv chi.LFunction s -
          logDeriv chi.primitiveCharacter.LFunction s).re ≤
            ‖logDeriv chi.LFunction s -
              logDeriv chi.primitiveCharacter.LFunction s‖ :=
      calc
        -(logDeriv chi.LFunction s -
            logDeriv chi.primitiveCharacter.LFunction s).re ≤
            |-(logDeriv chi.LFunction s -
              logDeriv chi.primitiveCharacter.LFunction s).re| := le_abs_self _
        _ = |(logDeriv chi.LFunction s -
            logDeriv chi.primitiveCharacter.LFunction s).re| := abs_neg _
        _ ≤ ‖logDeriv chi.LFunction s -
            logDeriv chi.primitiveCharacter.LFunction s‖ :=
          Complex.abs_re_le_norm _
    have hIdentity :
        -(logDeriv chi.LFunction s).re =
          -(logDeriv chi.primitiveCharacter.LFunction s).re -
            (logDeriv chi.LFunction s -
              logDeriv chi.primitiveCharacter.LFunction s).re := by
      simp
      ring
    rw [hIdentity]
    linarith
  calc
    -(logDeriv chi.LFunction s).re ≤
        -(logDeriv chi.primitiveCharacter.LFunction s).re + Real.log N :=
      hDifferenceReal
    _ ≤ A * (Real.log N + Real.log (|s.im| + 2)) + Real.log N :=
      add_le_add hPrimitiveAmbient le_rfl
    _ ≤ (A + 1) * (Real.log N + Real.log (|s.im| + 2)) := by
      nlinarith [mul_nonneg hAPos.le hLogNNonneg,
        mul_nonneg hAPos.le hLogHeightNonneg]

end BombieriVinogradov.SiegelWalfisz
