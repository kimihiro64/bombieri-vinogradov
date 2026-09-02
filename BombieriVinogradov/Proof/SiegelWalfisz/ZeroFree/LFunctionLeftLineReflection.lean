import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedRegularLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorNearOriginDifferentiability
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionZeroLowerStrip

/-!
# Reflection identity for the L-function logarithmic derivative

This module expands the completed functional equation on both sides and solves
exactly for the ordinary L-function logarithmic derivative on the left line.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_LFunction_left_line_eq_reflected
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hsRe : s.re = -(1 : Real) / 2) :
    logDeriv chi.LFunction s =
      -(Real.log N : Complex) -
        logDeriv (Inv.inv chi).LFunction (1 - s) -
        logDeriv (Inv.inv chi).gammaFactor (1 - s) -
        logDeriv chi.gammaFactor s := by
  have hsRange : -1 < s.re := by
    rw [hsRe]
    norm_num
  have hs0 : Ne s 0 := by
    intro hsZero
    rw [hsZero] at hsRe
    norm_num at hsRe
  have hLFunctionNe : Ne (chi.LFunction s) 0 := by
    intro hZero
    have hPositive :=
      re_pos_of_LFunction_eq_zero_of_neg_one_lt_re
        hchi hPrimitive hsRange hs0 hZero
    rw [hsRe] at hPositive
    norm_num at hPositive
  have hGammaNe : Ne (chi.gammaFactor s) 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_neg_one_lt_re_of_ne_zero
      chi hsRange hs0
  have hGammaDifferentiable :
      DifferentiableAt Complex chi.gammaFactor s :=
    DirichletCharacter.differentiableAt_gammaFactor_of_neg_one_lt_re_of_ne_zero
      chi hsRange hs0
  have hLeft :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular
      hchi hLFunctionNe hGammaNe hGammaDifferentiable
  have hInvNe : Ne (Inv.inv chi) 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hRightRe : 1 < (1 - s).re := by
    rw [Complex.sub_re, hsRe]
    norm_num
  have hRight :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors
      hInvNe hRightRe
  have hReflectionRaw :=
    logDeriv_symmetricCompletedLFunction_one_sub
      hchi hPrimitive (1 - s)
  have hReflection :
      logDeriv (symmetricCompletedLFunction chi) s =
        -logDeriv (symmetricCompletedLFunction (Inv.inv chi)) (1 - s) := by
    simpa using hReflectionRaw
  rw [hLeft, hRight] at hReflection
  linear_combination hReflection

end BombieriVinogradov.SiegelWalfisz
