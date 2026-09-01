import BombieriVinogradov.Helpers.ComplexAnalysis.AnalyticOrderConjugation
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveRootNumberNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFunctionalEquation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import Mathlib.Analysis.Analytic.Order

/-!
# Multiplicity symmetry for completed-function zeros

This module combines complex conjugation with the functional equation to prove that
the analytic zero order is invariant under `rho` mapping to `1 - conj rho`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem analyticOrderNatAt_symmetricCompletedLFunction_inv_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (rho : Complex) :
    analyticOrderNatAt (symmetricCompletedLFunction chi⁻¹)
        ((starRingEnd Complex) rho) =
      analyticOrderNatAt (symmetricCompletedLFunction chi) rho := by
  have hAnalytic :
      AnalyticAt Complex (symmetricCompletedLFunction chi) rho :=
    (differentiable_symmetricCompletedLFunction hchi).analyticAt rho
  have hOrder :=
    BombieriVinogradov.ComplexAnalysis.AnalyticAt.analyticOrderNatAt_conj_conj
        (f := symmetricCompletedLFunction chi)
        (z := (starRingEnd Complex) rho)
        (by simpa [Complex.conj_conj] using hAnalytic)
  have hFunctions :
      (fun w : Complex =>
        (starRingEnd Complex)
          (symmetricCompletedLFunction chi ((starRingEnd Complex) w))) =
        symmetricCompletedLFunction chi⁻¹ := by
    funext w
    exact (symmetricCompletedLFunction_inv_eq_conj_conj hchi w).symm
  rw [hFunctions, Complex.conj_conj] at hOrder
  exact hOrder

theorem analyticOrderNatAt_symmetricCompletedLFunction_one_sub
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (s : Complex) :
    analyticOrderNatAt (symmetricCompletedLFunction chi) (1 - s) =
      analyticOrderNatAt (symmetricCompletedLFunction chi⁻¹) s := by
  let reflect : Complex -> Complex := fun w => 1 - w
  have hReflectAnalytic : AnalyticAt Complex reflect s := by
    fun_prop
  have hReflectDeriv : deriv reflect s ≠ 0 := by
    simp [reflect]
  have hCompositionOrder :=
    analyticOrderAt_comp_of_deriv_ne_zero
      (f := symmetricCompletedLFunction chi) (g := reflect) (z₀ := s)
      hReflectAnalytic hReflectDeriv
  have hCompositionOrderNat :
      analyticOrderNatAt
          (fun w : Complex => symmetricCompletedLFunction chi (1 - w)) s =
        analyticOrderNatAt (symmetricCompletedLFunction chi) (1 - s) := by
    simpa [analyticOrderNatAt, reflect, Function.comp_def] using
      congrArg ENat.toNat hCompositionOrder
  have hInverseNe : chi⁻¹ ≠ 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hInverseAnalytic :
      AnalyticAt Complex (symmetricCompletedLFunction chi⁻¹) s :=
    (differentiable_symmetricCompletedLFunction hInverseNe).analyticAt s
  have hRootNe := BombieriVinogradov.primitive_rootNumber_ne_zero hPrimitive
  have hRootOrder :
      analyticOrderAt (fun _w : Complex => chi.rootNumber) s = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr hRootNe
  have hProductOrder :
      analyticOrderAt
          (fun w : Complex =>
            chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w) s =
        analyticOrderAt (symmetricCompletedLFunction chi⁻¹) s := by
    change analyticOrderAt
        ((fun _w : Complex => chi.rootNumber) *
          symmetricCompletedLFunction chi⁻¹) s = _
    rw [analyticOrderAt_mul analyticAt_const hInverseAnalytic, hRootOrder, zero_add]
  have hProductOrderNat :
      analyticOrderNatAt
          (fun w : Complex =>
            chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w) s =
        analyticOrderNatAt (symmetricCompletedLFunction chi⁻¹) s := by
    simpa [analyticOrderNatAt] using congrArg ENat.toNat hProductOrder
  have hFunctions :
      (fun w : Complex => symmetricCompletedLFunction chi (1 - w)) =
        fun w : Complex =>
          chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w := by
    funext w
    exact symmetricCompletedLFunction_one_sub hPrimitive w
  calc
    analyticOrderNatAt (symmetricCompletedLFunction chi) (1 - s) =
        analyticOrderNatAt
          (fun w : Complex => symmetricCompletedLFunction chi (1 - w)) s :=
      hCompositionOrderNat.symm
    _ = analyticOrderNatAt
          (fun w : Complex =>
            chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w) s := by
      rw [hFunctions]
    _ = analyticOrderNatAt (symmetricCompletedLFunction chi⁻¹) s :=
      hProductOrderNat

theorem analyticOrderNatAt_symmetricCompletedLFunction_one_sub_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (rho : Complex) :
    analyticOrderNatAt (symmetricCompletedLFunction chi)
        (1 - (starRingEnd Complex) rho) =
      analyticOrderNatAt (symmetricCompletedLFunction chi) rho := by
  calc
    analyticOrderNatAt (symmetricCompletedLFunction chi)
        (1 - (starRingEnd Complex) rho) =
      analyticOrderNatAt (symmetricCompletedLFunction chi⁻¹)
        ((starRingEnd Complex) rho) :=
      analyticOrderNatAt_symmetricCompletedLFunction_one_sub
        hchi hPrimitive ((starRingEnd Complex) rho)
    _ = analyticOrderNatAt (symmetricCompletedLFunction chi) rho :=
      analyticOrderNatAt_symmetricCompletedLFunction_inv_conj hchi rho

end BombieriVinogradov.SiegelWalfisz
