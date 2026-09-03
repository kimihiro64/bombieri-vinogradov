import BombieriVinogradov.Helpers.ComplexAnalysis.ReciprocalImaginaryGap
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Reciprocal bounds in positive retained zero bands

This module specializes the imaginary-part reciprocal bound to retained zeros
whose absolute ordinates lie in a positive-index unit band.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_one_div_retainedCriticalZeroBand_le_one_div
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex} {k : Nat}
    {p : SymmetricCompletedZeroIndex chi}
    (hk : 1 <= k)
    (hp : (retainedCriticalZeroBand chi T exceptional k :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    norm (1 / symmetricCompletedZeroValue p) <= 1 / (k : Real) := by
  have hkNat : 0 < k := Nat.zero_lt_of_lt hk
  have hkReal : 0 < (k : Real) := (Nat.cast_pos).2 hkNat
  have hBand :
      (k : Real) <= abs (symmetricCompletedZeroValue p).im :=
    ((mem_retainedCriticalZeroBand_iff).mp hp).2.1
  exact
    BombieriVinogradov.ComplexAnalysis.norm_one_div_le_one_div_of_le_abs_im
      hkReal hBand

end BombieriVinogradov.SiegelWalfisz
