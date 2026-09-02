import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.ExceptionalResidueValues
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Exceptional residue sums

This module evaluates the residue sum over the optional exceptional-zero pair.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The residue sum over an absent exceptional-zero pair vanishes. -/
theorem sum_residue_regularizedExplicitFormulaIntegrand_exceptionalZeroValues_none
    {N x : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Finset.sum (exceptionalZeroValues none)
        (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) = 0 := by
  simp [exceptionalZeroValues]

/-- The residue sum over a distinct simple exceptional-zero pair is the sum of its two terms. -/
theorem sum_residue_regularizedExplicitFormulaIntegrand_exceptionalZeroValues_some
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) (hx : 0 < x) {c : Real} {beta : Complex}
    (hExceptional : IsExceptionalZero c chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1)
    (hDistinct : Ne beta (1 - beta)) :
    Finset.sum (exceptionalZeroValues (some beta))
        (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) =
      -((x : Complex) ^ beta / beta) +
        -((x : Complex) ^ (1 - beta) / (1 - beta)) := by
  unfold exceptionalZeroValues
  rw [Finset.sum_insert (by simpa using hDistinct)]
  rw [Finset.sum_singleton]
  rw [residue_regularizedExplicitFormulaIntegrand_exceptionalZero
    hchi hx hExceptional hSimple]
  rw [residue_regularizedExplicitFormulaIntegrand_exceptionalReflection
    hchi hPrimitive hSquare hx hExceptional hSimple]

end BombieriVinogradov.SiegelWalfisz
