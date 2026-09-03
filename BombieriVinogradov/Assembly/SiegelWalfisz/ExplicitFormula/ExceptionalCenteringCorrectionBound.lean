import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalCorrection
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ComplexDifferenceQuotient
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ReciprocalBound
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exceptional-zero centering correction bound

The centered residue identity, nonsingular reciprocal bound and reflected
difference-quotient estimate give the published secondary error scale.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_centeredExceptionalResidueSum_add_exceptionalZeroContribution_le
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) (hx : 2 < x) {c : Real} {beta : Complex}
    (hExceptional : IsExceptionalZero c chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1)
    (hDistinct : Ne beta (1 - beta))
    (hLower : (3 / 4 : Real) <= beta.re) :
    norm (centeredExceptionalResidueSum chi x (some beta) +
        exceptionalZeroContribution x (some beta)) <=
      (4 / 3 : Real) + (x : Real) ^ (1 / 4 : Real) * Real.log x := by
  have hxNat : 3 <= x := Nat.succ_le_iff.mpr hx
  have hxRealThree : (3 : Real) <= (x : Real) := (Nat.cast_le).2 hxNat
  have hxReal : (1 : Real) <= (x : Real) := by linarith
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hReflected :
      norm (((x : Complex) ^ (1 - beta) - 1) / (1 - beta)) <=
        (x : Real) ^ (1 / 4 : Real) * Real.log x := by
    simpa only [Complex.ofReal_natCast] using
      norm_reflectedCpowDifferenceQuotient_le hxReal
        hExceptional.2.1 hLower hExceptional.2.2.2.1
  have hReciprocal : norm ((1 : Complex) / beta) <= (4 / 3 : Real) :=
    norm_one_div_le_four_thirds_of_three_quarters_le_re hLower
  rw [centeredExceptionalResidueSum_add_exceptionalZeroContribution
    hchi hPrimitive hSquare hxPos hExceptional hSimple hDistinct]
  exact (norm_sub_le _ _).trans (add_le_add hReciprocal hReflected)

end BombieriVinogradov.SiegelWalfisz
