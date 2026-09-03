import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindow
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith

/-!
# Absolute-height bands lie in two vertical windows
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem mem_pos_or_neg_zeroHeightWindow_of_mem_retainedCriticalZeroBand
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex} {k : Nat}
    {p : SymmetricCompletedZeroIndex chi}
    (hp : (retainedCriticalZeroBand chi T exceptional k :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    Or
      ((zeroHeightWindow (chi := chi) (k : Real)) p)
      ((zeroHeightWindow (chi := chi) (-(k : Real))) p) := by
  have hBand := mem_retainedCriticalZeroBand_iff.mp hp
  have hLower :
      (k : Real) <= abs (symmetricCompletedZeroValue p).im :=
    hBand.2.1
  have hUpper :
      abs (symmetricCompletedZeroValue p).im <
        ((k + 1 : Nat) : Real) :=
    hBand.2.2
  rw [Nat.cast_add, Nat.cast_one] at hUpper
  by_cases hIm : 0 <= (symmetricCompletedZeroValue p).im
  case pos =>
    apply Or.inl
    change abs ((k : Real) - (symmetricCompletedZeroValue p).im) < 1
    rw [abs_of_nonneg hIm] at hLower hUpper
    rw [abs_of_nonpos (sub_nonpos.mpr hLower)]
    linarith
  case neg =>
    apply Or.inr
    change abs (-(k : Real) - (symmetricCompletedZeroValue p).im) < 1
    have hImNeg : (symmetricCompletedZeroValue p).im < 0 :=
      lt_of_not_ge hIm
    rw [abs_of_neg hImNeg] at hLower hUpper
    have hExpressionNonneg :
        0 <= -(k : Real) - (symmetricCompletedZeroValue p).im := by
      linarith
    rw [abs_of_nonneg hExpressionNonneg]
    linarith

end BombieriVinogradov.SiegelWalfisz
