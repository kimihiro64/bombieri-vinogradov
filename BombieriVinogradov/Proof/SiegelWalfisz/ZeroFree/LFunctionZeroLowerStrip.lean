import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorNearOrigin
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Primitive L-function zeros near the critical strip

This module isolates the functional-equation argument that rules out nonzero
primitive Dirichlet L-function zeros immediately to the left of the critical
strip.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- A nonzero primitive Dirichlet L-function zero with real part greater than
minus one has positive real part. -/
theorem re_pos_of_LFunction_eq_zero_of_neg_one_lt_re
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hsLower : -1 < s.re) (hs0 : Ne s 0)
    (hzero : chi.LFunction s = 0) :
    0 < s.re := by
  have hGammaNe : Ne (chi.gammaFactor s) 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_neg_one_lt_re_of_ne_zero
      chi hsLower hs0
  have hCompletedProduct :
      chi.completedLFunction s = chi.LFunction s * chi.gammaFactor s := by
    exact ((eq_div_iff hGammaNe).mp
      (chi.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0))).symm
  have hSymmetricZero : symmetricCompletedLFunction chi s = 0 := by
    rw [symmetricCompletedLFunction, hCompletedProduct, hzero]
    simp
  by_contra hnot
  have hReflectedRe :
      1 <= (1 - (starRingEnd Complex) s).re := by
    have hConjRe : ((starRingEnd Complex) s).re = s.re := by simp
    rw [Complex.sub_re, hConjRe]
    norm_num
    linarith
  have hReflectedZero :
      symmetricCompletedLFunction chi
        (1 - (starRingEnd Complex) s) = 0 := by
    rw [symmetricCompletedLFunction_one_sub_conj hchi hPrimitive,
      hSymmetricZero, map_zero, mul_zero]
  exact symmetricCompletedLFunction_ne_zero_of_one_le_re
    hchi hReflectedRe hReflectedZero

end BombieriVinogradov.SiegelWalfisz
