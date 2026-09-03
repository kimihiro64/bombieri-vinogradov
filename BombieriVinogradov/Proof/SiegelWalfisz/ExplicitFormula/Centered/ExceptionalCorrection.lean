import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Ring

/-!
# Exact exceptional-zero centering correction

Adding the advertised exceptional term to the centered exceptional residue
sum leaves one reciprocal and the reflected difference quotient.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem centeredExceptionalResidueSum_add_exceptionalZeroContribution
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) (hx : 0 < x) {c : Real} {beta : Complex}
    (hExceptional : IsExceptionalZero c chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1)
    (hDistinct : Ne beta (1 - beta)) :
    centeredExceptionalResidueSum chi x (some beta) +
        exceptionalZeroContribution x (some beta) =
      (1 : Complex) / beta -
        ((x : Complex) ^ (1 - beta) - 1) / (1 - beta) := by
  rw [centeredExceptionalResidueSum_some
    hchi hPrimitive hSquare hx hExceptional hSimple hDistinct]
  unfold exceptionalZeroContribution
  ring

end BombieriVinogradov.SiegelWalfisz
