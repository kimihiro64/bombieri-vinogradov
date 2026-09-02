import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerProduct
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionNonvanishing
import Mathlib.Analysis.Analytic.Order

/-!
# Analytic order under a finite level correction

The finite Euler correction between an imprimitive Dirichlet L-function and
the L-function of its primitive character is analytic and nonvanishing in the
positive half-plane. It therefore does not change analytic zero order there.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem analyticOrderNatAt_LFunction_eq_primitive
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : chi ≠ 1)
    {s : Complex} (hs : 0 < s.re) :
    analyticOrderNatAt chi.LFunction s =
      analyticOrderNatAt chi.primitiveCharacter.LFunction s := by
  have hPrimitiveNe :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi
  have hPrimitiveAnalytic :
      AnalyticAt Complex chi.primitiveCharacter.LFunction s :=
    (DirichletCharacter.differentiable_LFunction hPrimitiveNe).analyticAt s
  have hCorrectionDifferentiable :
      Differentiable Complex (levelCorrection chi) := by
    intro z
    change DifferentiableAt Complex
      (fun w : Complex =>
        ∏ p ∈ N.primeFactors, levelCorrectionFactor chi p w) z
    exact DifferentiableAt.fun_finsetProd (fun p hp =>
      differentiableAt_levelCorrectionFactor chi
        (Nat.prime_of_mem_primeFactors hp) z)
  have hCorrectionAnalytic :
      AnalyticAt Complex (levelCorrection chi) s :=
    hCorrectionDifferentiable.analyticAt s
  have hCorrectionNe : levelCorrection chi s ≠ 0 :=
    levelCorrection_ne_zero_of_re_pos chi hs
  have hCorrectionOrder : analyticOrderAt (levelCorrection chi) s = 0 :=
    hCorrectionAnalytic.analyticOrderAt_eq_zero.mpr hCorrectionNe
  have hFunctions : chi.LFunction =
      fun z => chi.primitiveCharacter.LFunction z * levelCorrection chi z := by
    funext z
    exact LFunction_eq_primitive_mul_levelCorrection chi hchi z
  have hOrder : analyticOrderAt chi.LFunction s =
      analyticOrderAt chi.primitiveCharacter.LFunction s := by
    rw [hFunctions]
    change analyticOrderAt
      (chi.primitiveCharacter.LFunction * levelCorrection chi) s = _
    rw [analyticOrderAt_mul hPrimitiveAnalytic hCorrectionAnalytic]
    rw [hCorrectionOrder, add_zero]
  simpa [analyticOrderNatAt] using congrArg ENat.toNat hOrder

end BombieriVinogradov.SiegelWalfisz
