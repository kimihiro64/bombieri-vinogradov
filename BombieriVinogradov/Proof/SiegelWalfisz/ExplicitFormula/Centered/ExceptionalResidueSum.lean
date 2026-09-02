import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.ExceptionalResidueSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered exceptional residue sum

This module subtracts the x equals one exceptional residue sum, producing the
two difference quotients used in the centered explicit formula.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered exceptional residue sum is its x-value minus its value at one. -/
def centeredExceptionalResidueSum
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (exceptional : Option Complex) : Complex :=
  Finset.sum (exceptionalZeroValues exceptional)
      (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) -
    Finset.sum (exceptionalZeroValues exceptional)
      (fun rho => residue (regularizedExplicitFormulaIntegrand chi 1) rho)

/-- The centered exceptional residue sum vanishes when no exceptional zero is selected. -/
theorem centeredExceptionalResidueSum_none
    {N x : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    centeredExceptionalResidueSum chi x none = 0 := by
  simp [centeredExceptionalResidueSum, exceptionalZeroValues]

/-- A selected simple exceptional pair contributes two negative difference quotients. -/
theorem centeredExceptionalResidueSum_some
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSquare : chi ^ 2 = 1) (hx : 0 < x) {c : Real} {beta : Complex}
    (hExceptional : IsExceptionalZero c chi beta)
    (hSimple : analyticOrderNatAt chi.LFunction beta = 1)
    (hDistinct : Ne beta (1 - beta)) :
    centeredExceptionalResidueSum chi x (some beta) =
      -(((x : Complex) ^ beta - 1) / beta) +
        -(((x : Complex) ^ (1 - beta) - 1) / (1 - beta)) := by
  unfold centeredExceptionalResidueSum
  rw [sum_residue_regularizedExplicitFormulaIntegrand_exceptionalZeroValues_some
    hchi hPrimitive hSquare hx hExceptional hSimple hDistinct]
  rw [sum_residue_regularizedExplicitFormulaIntegrand_exceptionalZeroValues_some
    hchi hPrimitive hSquare (by norm_num) hExceptional hSimple hDistinct]
  simp
  ring

end BombieriVinogradov.SiegelWalfisz
