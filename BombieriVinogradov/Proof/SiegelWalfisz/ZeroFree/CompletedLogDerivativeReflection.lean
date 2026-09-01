import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveRootNumberNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFunctionalEquation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Reflection of the completed-function logarithmic derivative

This module differentiates the primitive symmetric functional equation. The affine
reflection contributes the minus sign, while the nonzero root number disappears from
the logarithmic derivative.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_symmetricCompletedLFunction_one_sub
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (s : Complex) :
    logDeriv (symmetricCompletedLFunction chi) (1 - s) =
      -logDeriv (symmetricCompletedLFunction chi⁻¹) s := by
  have hFunction :
      (fun w : Complex => symmetricCompletedLFunction chi (1 - w)) =
        fun w : Complex =>
          chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w := by
    funext w
    exact symmetricCompletedLFunction_one_sub hPrimitive w
  have hLeft :
      logDeriv (fun w : Complex => symmetricCompletedLFunction chi (1 - w)) s =
        -logDeriv (symmetricCompletedLFunction chi) (1 - s) := by
    have hComp := logDeriv_comp
      (f := symmetricCompletedLFunction chi)
      (g := fun w : Complex => 1 - w)
      (x := s)
      ((differentiable_symmetricCompletedLFunction hchi).differentiableAt)
      (by fun_prop)
    simpa [Function.comp_def] using hComp
  have hRight :
      logDeriv
          (fun w : Complex =>
            chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w) s =
        logDeriv (symmetricCompletedLFunction chi⁻¹) s :=
    logDeriv_const_mul s chi.rootNumber
      (BombieriVinogradov.primitive_rootNumber_ne_zero hPrimitive)
  have hLogDerivEquality :
      logDeriv (fun w : Complex => symmetricCompletedLFunction chi (1 - w)) s =
        logDeriv
          (fun w : Complex =>
            chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w) s :=
    congrArg (fun f : Complex -> Complex => logDeriv f s) hFunction
  calc
    logDeriv (symmetricCompletedLFunction chi) (1 - s) =
        -logDeriv
          (fun w : Complex => symmetricCompletedLFunction chi (1 - w)) s := by
      rw [hLeft]
      ring
    _ = -logDeriv
          (fun w : Complex =>
            chi.rootNumber * symmetricCompletedLFunction chi⁻¹ w) s := by
      rw [hLogDerivEquality]
    _ = -logDeriv (symmetricCompletedLFunction chi⁻¹) s := by
      rw [hRight]

end BombieriVinogradov.SiegelWalfisz
