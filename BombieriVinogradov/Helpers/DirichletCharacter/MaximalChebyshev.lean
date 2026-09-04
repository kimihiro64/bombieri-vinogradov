import BombieriVinogradov.Definitions.VaughanMeanValue
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Basic bounds for the finite maximal character sum

The endpoint range includes zero and every natural endpoint
at most the real cutoff's natural floor.
-/
set_option autoImplicit false

namespace BombieriVinogradov.VaughanMeanValue

theorem norm_psiCharacterSum_le_maximalPsiNorm {X : Real} {y q : Nat}
    (chi : _root_.DirichletCharacter Complex q) (hy : y <= Nat.floor X) :
    norm (psiCharacterSum y q chi) <= maximalPsiNorm X chi := by
  unfold maximalPsiNorm
  exact Finset.le_sup' (fun n => norm (psiCharacterSum n q chi))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hy))

theorem maximalPsiNorm_nonneg (X : Real) {q : Nat}
    (chi : _root_.DirichletCharacter Complex q) : 0 <= maximalPsiNorm X chi :=
  (norm_nonneg (psiCharacterSum 0 q chi)).trans
    (norm_psiCharacterSum_le_maximalPsiNorm chi (Nat.zero_le _))

end BombieriVinogradov.VaughanMeanValue
