import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorRegularity

/-!
# Product formula for completed Dirichlet L-functions

This module identifies Mathlib's completed Dirichlet L-function with the product of
the ordinary L-function and its gamma factor in the positive half-plane.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 0 < s.re) :
    chi.completedLFunction s = chi.LFunction s * chi.gammaFactor s := by
  have hsNeZero : s ≠ 0 := by
    intro hsZero
    subst s
    norm_num at hs
  have hGammaNe :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hs
  exact ((eq_div_iff hGammaNe).mp
    (chi.LFunction_eq_completed_div_gammaFactor s (.inl hsNeZero))).symm

theorem DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_one_lt_re
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    chi.completedLFunction s = chi.LFunction s * chi.gammaFactor s :=
  DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
    chi (lt_trans zero_lt_one hs)

end BombieriVinogradov.SiegelWalfisz
