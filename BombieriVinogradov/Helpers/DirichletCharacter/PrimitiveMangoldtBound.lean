import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.ArithmeticFunction.NonCoprimeMangoldtBound
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveSumDifference
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Primitive-character comparison for Mangoldt norms

The ambient character sum differs from its primitive twist only
by a logarithmically bounded contribution at the missing Euler factors.
-/
set_option autoImplicit false

namespace BombieriVinogradov.VaughanMeanValue

theorem norm_psiCharacterSum_le_primitive_add_log_mul_log
    {N x : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N) (hx : 0 < x) :
    norm (psiCharacterSum x N chi) <=
      norm (psiCharacterSum x chi.conductor chi.primitiveCharacter) +
        Real.log N * Real.log x / Real.log (2 : Real) := by
  exact (norm_le_norm_add_norm_sub' (psiCharacterSum x N chi)
    (psiCharacterSum x chi.conductor chi.primitiveCharacter)).trans
    (add_le_add (le_refl _) ((norm_psiCharacterSum_sub_primitive_le_mangoldt chi x).trans
      (nonCoprimeMangoldtSum_le_log_mul_log (NeZero.ne N) hx)))

end BombieriVinogradov.VaughanMeanValue
