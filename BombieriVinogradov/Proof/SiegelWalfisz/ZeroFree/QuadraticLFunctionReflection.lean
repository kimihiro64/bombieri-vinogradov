import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLFunctionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroMultiplicitySymmetry
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroSymmetry
import Mathlib.Analysis.Analytic.Order

/-!
# Reflection of primitive quadratic L-function zeros

This module transfers both zero values and analytic multiplicities across
the functional-equation reflection for primitive quadratic characters.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A primitive quadratic L-function zero in the critical strip reflects to a zero at one minus that point. -/
theorem LFunction_one_sub_eq_zero_of_quadratic
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) {beta : Complex}
    (hBetaPos : 0 < beta.re) (hBetaLt : beta.re < 1)
    (hBetaZero : chi.LFunction beta = 0) :
    chi.LFunction (1 - beta) = 0 := by
  have hCompletedBeta : symmetricCompletedLFunction chi beta = 0 := by
    rw [symmetricCompletedLFunction,
      DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
        chi hBetaPos]
    simp [hBetaZero]
  have hCompletedReflect : symmetricCompletedLFunction chi (1 - beta) = 0 := by
    have hReflect :=
      (symmetricCompletedLFunction_eq_zero_iff_inv_one_sub
        hPrimitive beta).mp hCompletedBeta
    have hInvSelf :=
      BombieriVinogradov.DirichletCharacter.inv_eq_self_of_sq_eq_one
        chi hSquare
    rw [hInvSelf] at hReflect
    exact hReflect
  have hReflectPos : 0 < (1 - beta).re := by
    change 0 < 1 - beta.re
    linarith
  have hProduct :
      DirichletCharacter.completedLFunction chi (1 - beta) =
        chi.LFunction (1 - beta) * chi.gammaFactor (1 - beta) :=
    DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
      chi hReflectPos
  rw [symmetricCompletedLFunction, hProduct] at hCompletedReflect
  have hN : Ne (N : Complex) 0 := by
    exact_mod_cast NeZero.ne N
  have hNormalizationNe :
      Ne ((N : Complex) ^ ((1 - beta) / 2)) 0 := by
    simp [hN]
  have hGammaNe : Ne (chi.gammaFactor (1 - beta)) 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hReflectPos
  have hInnerZero :
      chi.LFunction (1 - beta) * chi.gammaFactor (1 - beta) = 0 :=
    (mul_eq_zero.mp hCompletedReflect).resolve_left hNormalizationNe
  exact (mul_eq_zero.mp hInnerZero).resolve_right hGammaNe

/-- The analytic multiplicities of a primitive quadratic L-function at beta and one minus beta agree. -/
theorem analyticOrderNatAt_LFunction_one_sub_of_quadratic
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) {beta : Complex}
    (hBetaPos : 0 < beta.re) (hBetaLt : beta.re < 1) :
    analyticOrderNatAt chi.LFunction (1 - beta) =
      analyticOrderNatAt chi.LFunction beta := by
  have hReflectPos : 0 < (1 - beta).re := by
    change 0 < 1 - beta.re
    linarith
  have hOrderSymmetry :=
    analyticOrderNatAt_symmetricCompletedLFunction_one_sub
      hchi hPrimitive beta
  have hInvSelf :=
    BombieriVinogradov.DirichletCharacter.inv_eq_self_of_sq_eq_one
      chi hSquare
  rw [hInvSelf] at hOrderSymmetry
  calc
    analyticOrderNatAt chi.LFunction (1 - beta) =
        analyticOrderNatAt (symmetricCompletedLFunction chi) (1 - beta) :=
      (analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction
        hchi hReflectPos).symm
    _ = analyticOrderNatAt (symmetricCompletedLFunction chi) beta :=
      hOrderSymmetry
    _ = analyticOrderNatAt chi.LFunction beta :=
      analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction
        hchi hBetaPos

end BombieriVinogradov.SiegelWalfisz
