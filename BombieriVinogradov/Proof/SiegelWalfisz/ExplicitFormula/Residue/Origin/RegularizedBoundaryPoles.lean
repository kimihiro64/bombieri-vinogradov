import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedMeromorphic
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Boundary pole exclusion for the regularized integrand

This module transfers a zero-free rectangle-border condition from the original
explicit-formula integrand to its origin-regularized form.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- If the original integrand has no poles on a rectangle border and the
border avoids zero, then the regularized integrand also has no border poles. -/
theorem disjoint_regularizedExplicitFormulaIntegrand_poles_boundary
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) (z w : Complex)
    (horiginal : Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi x) p < 0})
    (hzero : Not (Membership.mem (RectangleBorder z w) 0)) :
    Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt
        (regularizedExplicitFormulaIntegrand chi x) p < 0} := by
  rw [Set.disjoint_left]
  intro p hpBorder hpRegularizedPole
  have hpNe : Ne p 0 := by
    intro hpZero
    apply hzero
    simpa [hpZero] using hpBorder
  have hOriginalNonneg :
      0 <= meromorphicOrderAt (explicitFormulaIntegrand chi x) p := by
    apply le_of_not_gt
    intro hpOriginalPole
    exact Set.disjoint_left.mp horiginal hpBorder hpOriginalPole
  have hCorrectionAnalytic :
      AnalyticAt Complex (originDoublePoleCorrection chi) p := by
    unfold originDoublePoleCorrection
    exact (analyticAt_const
      (v := (lFunctionOriginMultiplicity chi : Complex)) (x := p)).div
        (by fun_prop) (pow_ne_zero 2 hpNe)
  have hCorrectionNonneg :
      0 <= meromorphicOrderAt (originDoublePoleCorrection chi) p :=
    hCorrectionAnalytic.meromorphicOrderAt_nonneg
  have hSumNonneg :
      0 <= meromorphicOrderAt
        (explicitFormulaIntegrand chi x + originDoublePoleCorrection chi) p :=
    (le_min hOriginalNonneg hCorrectionNonneg).trans
      (meromorphicOrderAt_add
        (meromorphic_explicitFormulaIntegrand hchi x hx p)
        hCorrectionAnalytic.meromorphicAt)
  apply (not_lt_of_ge hSumNonneg)
  exact hpRegularizedPole

end BombieriVinogradov.SiegelWalfisz
