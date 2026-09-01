import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardConstant
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeRealZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernelSubset

/-!
# Selectable-zero logarithmic-derivative bound

This module proves Strombergsson Lemma 11.3 with an explicit uniform existential
constant and an arbitrary subset of the multiplicity-indexed nontrivial zeros.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_selectableZero_logDeriv_bound :
    exists A : Real, 0 < A ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {s : Complex}, 1 < s.re -> s.re ≤ 2 ->
              forall selected : Set (SymmetricCompletedZeroIndex chi),
                -(logDeriv chi.LFunction s).re ≤
                  -(∑' p : selected,
                    (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p.1)).re) +
                    A * (Real.log N + Real.log (|s.im| + 2)) := by
  obtain ⟨Cgamma, hCgammaPos, hGamma⟩ :=
    exists_norm_logDeriv_gammaFactor_le_log
  refine Exists.intro (Cgamma + 1)
    (And.intro (add_pos hCgammaPos zero_lt_one) ?_)
  intro N _hN hNLower chi hchi hPrimitive s hsLower hsUpper selected
  have hInverseNe : chi⁻¹ ≠ 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hPrimitiveInv : DirichletCharacter.IsPrimitive chi⁻¹ :=
    BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  obtain ⟨Bchi, hBchi, _hBchiUnique⟩ :=
    existsUnique_symmetricCompletedLFunction_hadamardConstant hchi hPrimitive
  obtain ⟨Binv, hBinv, _hBinvUnique⟩ :=
    existsUnique_symmetricCompletedLFunction_hadamardConstant
      hInverseNe hPrimitiveInv
  have hIdentity :=
    neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel
      hchi hPrimitive hBchi hBinv hsLower
  have hGammaNorm := hGamma chi hsLower hsUpper
  have hGammaRe :
      (logDeriv chi.gammaFactor s).re ≤
        Cgamma * Real.log (|s.im| + 2) :=
    (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans hGammaNorm
  have hSelected :=
    tsum_symmetricCompletedLFunction_zeroKernel_subtype_le
      hchi hPrimitive hsLower selected
  have hLogNNonneg : 0 ≤ Real.log N := by
    apply Real.log_nonneg
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hNLower)
  have hLogHeightNonneg : 0 ≤ Real.log (|s.im| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg s.im]
  have hRemainder :
      Real.log N / 2 + Cgamma * Real.log (|s.im| + 2) ≤
        (Cgamma + 1) * (Real.log N + Real.log (|s.im| + 2)) := by
    nlinarith [mul_nonneg hCgammaPos.le hLogNNonneg,
      mul_nonneg hCgammaPos.le hLogHeightNonneg]
  calc
    -(logDeriv chi.LFunction s).re =
        Real.log N / 2 + (logDeriv chi.gammaFactor s).re -
          ∑' p : SymmetricCompletedZeroIndex chi,
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re :=
      hIdentity
    _ ≤ Real.log N / 2 + Cgamma * Real.log (|s.im| + 2) -
        ∑' p : SymmetricCompletedZeroIndex chi,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
      exact sub_le_sub_right (add_le_add le_rfl hGammaRe) _
    _ ≤ Real.log N / 2 + Cgamma * Real.log (|s.im| + 2) -
        ∑' p : selected,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p.1)).re := by
      exact sub_le_sub_left hSelected _
    _ ≤ -(∑' p : selected,
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p.1)).re) +
        (Cgamma + 1) * (Real.log N + Real.log (|s.im| + 2)) := by
      linarith

end BombieriVinogradov.SiegelWalfisz
