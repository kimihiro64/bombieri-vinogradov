import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.LFunctionNonvanishing
import Mathlib.Tactic.Linarith

/-!
# Nonvanishing from a quantitative completed-zero ordinate gap

This module converts a positive reciprocal separation bound into the exact
qualitative avoidance interface used by horizontal-strip nonvanishing.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_ne_zero_of_completedZero_ordinate_gap
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T K L : Real} {s : Complex} (hsIm : s.im = T)
    (hsLower : -(1 : Real) / 2 <= s.re) (hT : Ne T 0)
    (hDenPos : 0 < K * L)
    (hGap : forall p : SymmetricCompletedZeroIndex chi,
      1 / (K * L) <=
        abs (T - (symmetricCompletedZeroValue p).im)) :
    Ne (chi.LFunction s) 0 := by
  apply LFunction_ne_zero_of_completedZero_ordinate_avoidance
    hchi hPrimitive hsIm hsLower hT
  intro p hEq
  have hGapP := hGap p
  rw [hEq, sub_self, abs_zero] at hGapP
  have hInvPos : 0 < 1 / (K * L) :=
    one_div_pos.mpr hDenPos
  linarith

end BombieriVinogradov.SiegelWalfisz
