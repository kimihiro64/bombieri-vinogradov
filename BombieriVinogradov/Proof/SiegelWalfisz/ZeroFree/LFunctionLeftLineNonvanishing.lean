import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionZeroLowerStrip
import Mathlib.Tactic.NormNum

/-!
# L-function nonvanishing on the explicit-formula left line

This module exposes the primitive nonprincipal left-line nonvanishing fact
needed by reflection, continuity, and contour estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_ne_zero_of_re_eq_neg_one_half
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex} (hsRe : s.re = -(1 : Real) / 2) :
    Ne (chi.LFunction s) 0 := by
  have hsRange : -1 < s.re := by
    rw [hsRe]
    norm_num
  have hs0 : Ne s 0 := by
    intro hsZero
    rw [hsZero] at hsRe
    norm_num at hsRe
  intro hZero
  have hPositive :=
    re_pos_of_LFunction_eq_zero_of_neg_one_lt_re
      hchi hPrimitive hsRange hs0 hZero
  rw [hsRe] at hPositive
  norm_num at hPositive

end BombieriVinogradov.SiegelWalfisz
