import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.ArithmeticFunction.NonCoprimeMangoldtBound
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveSumDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Finite Euler correction of the character Chebyshev sum

Character agreement away from the ambient prime divisors and the complete
prime-power divisor bound give one absolute logarithmic correction.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterChebyshevSum_sub_primitive_le
    {N x : Nat} (hN : Ne N 0) (chi : _root_.DirichletCharacter Complex N)
    (hx : 0 < x) :
    norm (characterChebyshevSum x chi -
      characterChebyshevSum x chi.primitiveCharacter) <=
        Real.log N * Real.log x / Real.log (2 : Real) := by
  change norm (VaughanMeanValue.psiCharacterSum x N chi -
    VaughanMeanValue.psiCharacterSum x chi.conductor chi.primitiveCharacter) <= _
  exact (VaughanMeanValue.norm_psiCharacterSum_sub_primitive_le_mangoldt chi x).trans
    (nonCoprimeMangoldtSum_le_log_mul_log hN hx)

end BombieriVinogradov.SiegelWalfisz
