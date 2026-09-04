import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Coefficient
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.NormNum

/-!
# The finite character Chebyshev sum at two

The summand at one vanishes; the remaining twisted Mangoldt coefficient
is bounded by log two uniformly in the character and its level.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterChebyshevSum_two_le_log_two
    {N : Nat} (chi : DirichletCharacter Complex N) :
    norm (characterChebyshevSum 2 chi) <= Real.log 2 := by
  have hValue : characterChebyshevSum 2 chi = twistedMangoldtSequence chi 2 := by
    norm_num [characterChebyshevSum,
      BombieriVinogradov.VaughanMeanValue.psiCharacterSum,
      twistedMangoldtSequence, Finset.sum_Icc_succ_top, mul_comm]
  rw [hValue]
  exact (norm_twistedMangoldtSequence_le_vonMangoldt chi 2).trans
    ArithmeticFunction.vonMangoldt_le_log

end BombieriVinogradov.SiegelWalfisz
