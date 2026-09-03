import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.EvenDerivativeNonzero
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.OddNonvanishing
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# L-function origin multiplicity bound
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem lFunctionOriginMultiplicity_le_one
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    lFunctionOriginMultiplicity chi <= 1 := by
  have hNNeOne : Ne N 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hAnalytic : AnalyticAt Complex chi.LFunction 0 :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt 0
  cases chi.even_or_odd with
  | inl hEven =>
      have hLZero : chi.LFunction 0 = 0 := by
        rw [DirichletCharacter.LFunction]
        rw [ZMod.LFunction_apply_zero_of_even hEven.to_fun]
        rw [chi.map_zero' hNNeOne]
        simp
      have hDerivative :=
        deriv_LFunction_zero_ne_zero_of_even hchi hPrimitive hEven
      have hOrder : analyticOrderAt chi.LFunction 0 = 1 :=
        hAnalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
          hLZero hDerivative
      unfold lFunctionOriginMultiplicity analyticOrderNatAt
      rw [hOrder]
      simp
  | inr hOdd =>
      have hNonzero :=
        LFunction_zero_ne_zero_of_odd hchi hPrimitive hOdd
      have hOrder : analyticOrderAt chi.LFunction 0 = 0 :=
        hAnalytic.analyticOrderAt_eq_zero.mpr hNonzero
      unfold lFunctionOriginMultiplicity analyticOrderNatAt
      rw [hOrder]
      simp

end BombieriVinogradov.SiegelWalfisz
