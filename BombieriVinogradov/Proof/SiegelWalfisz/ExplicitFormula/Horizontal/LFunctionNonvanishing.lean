import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndexOfLFunctionZero
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionZeroLowerStrip
import Mathlib.Tactic.Linarith

/-!
# Horizontal-strip L-function nonvanishing

This module converts separation from every completed-zero ordinate into
nonvanishing of the primitive L-function on a nonzero horizontal line.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem LFunction_ne_zero_of_completedZero_ordinate_avoidance
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} {s : Complex} (hsIm : s.im = T)
    (hsLower : -(1 : Real) / 2 <= s.re) (hT : Ne T 0)
    (hAvoid : forall p : SymmetricCompletedZeroIndex chi,
      Ne T (symmetricCompletedZeroValue p).im) :
    Ne (chi.LFunction s) 0 := by
  intro hzero
  have hsNe : Ne s 0 := by
    intro hsZero
    have hImZero := congrArg Complex.im hsZero
    rw [hsIm] at hImZero
    simp at hImZero
    exact hT hImZero
  have hsLowerWide : -1 < s.re := by linarith
  have hsPos : 0 < s.re :=
    re_pos_of_LFunction_eq_zero_of_neg_one_lt_re
      hchi hPrimitive hsLowerWide hsNe hzero
  choose p hp using
    exists_completedZeroIndex_of_LFunction_eq_zero
      hchi hPrimitive hsPos hzero
  change symmetricCompletedZeroValue p = s at hp
  have hIm := congrArg Complex.im hp
  have hValueIm : (symmetricCompletedZeroValue p).im = T := by
    rw [hIm, hsIm]
  exact hAvoid p hValueIm.symm

end BombieriVinogradov.SiegelWalfisz
