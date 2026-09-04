import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.PrimitiveMaximalSum
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveNonprincipalCard
import BombieriVinogradov.Helpers.RealAnalysis.FiniteAverageBound
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Primitive maximal averages with reciprocal-totient normalization

A uniform bound on nonprincipal character maxima survives the primitive
character sum and division by the positive modulus totient.
-/

set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- Normalize a common nonprincipal character bound by the totient. -/
theorem nonprincipalPrimitiveMaximalSum_div_totient_le
    {X K : Real} {N : Nat} [NeZero N] (hK : 0 <= K)
    (hBound : forall chi : _root_.DirichletCharacter Complex N,
      Ne chi 1 -> VaughanMeanValue.maximalPsiNorm X chi <= K) :
    nonprincipalPrimitiveMaximalSum X N / (N.totient : Real) <= K := by
  have hPhi : (0 : Real) < (N.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  have hCard : ((((LargeSieve.primitiveCharacters N).erase 1).card : Nat) : Real) <=
      (N.totient : Real) :=
    Nat.cast_le.mpr (DirichletCharacter.card_primitive_nonprincipal_le_totient (N := N))
  unfold nonprincipalPrimitiveMaximalSum
  exact RealAnalysis.sum_div_le_of_card_le
    ((LargeSieve.primitiveCharacters N).erase 1)
    (fun chi => VaughanMeanValue.maximalPsiNorm X chi)
    (t := (N.totient : Real)) (K := K) hPhi hCard hK
    (fun chi hchi => hBound chi (Finset.ne_of_mem_erase hchi))

end BombieriVinogradov.WeightedBombieriVinogradov
