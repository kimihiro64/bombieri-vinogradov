import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedMeromorphic
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.IntegrandSimpleAwayZero
import Mathlib.Analysis.Meromorphic.Order

/-!
# Pole order of the regularized integrand away from zero

This module proves only that the analytic double-pole correction cannot
worsen the previously established nonzero pole orders.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- At every nonzero point, the regularized explicit-formula integrand has
meromorphic order at least minus one. -/
theorem neg_one_le_meromorphicOrderAt_regularizedExplicitFormulaIntegrand_of_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x)
    {z : Complex} (hz : Ne z 0) :
    ((-1 : Int) : WithTop Int) <=
      meromorphicOrderAt (regularizedExplicitFormulaIntegrand chi x) z := by
  have hZeroNotMem :
      Not (Membership.mem ({z} : Set Complex) 0) := by
    simp [Ne.symm hz]
  have hOriginal :
      ((-1 : Int) : WithTop Int) <=
        meromorphicOrderAt (explicitFormulaIntegrand chi x) z :=
    hasSimplePolesOn_explicitFormulaIntegrand_away_zero
      hchi x hx ({z} : Set Complex) hZeroNotMem z (by simp)
  have hCorrectionAnalytic :
      AnalyticAt Complex (originDoublePoleCorrection chi) z := by
    unfold originDoublePoleCorrection
    exact (analyticAt_const
      (v := (lFunctionOriginMultiplicity chi : Complex)) (x := z)).div
        (by fun_prop) (pow_ne_zero 2 hz)
  have hCorrectionSimple :
      ((-1 : Int) : WithTop Int) <=
        meromorphicOrderAt (originDoublePoleCorrection chi) z := by
    have hNegOneLeZero :
        ((-1 : Int) : WithTop Int) <= ((0 : Int) : WithTop Int) :=
      WithTop.coe_le_coe.mpr (by omega)
    exact hNegOneLeZero.trans
      hCorrectionAnalytic.meromorphicOrderAt_nonneg
  change ((-1 : Int) : WithTop Int) <=
    meromorphicOrderAt
      (explicitFormulaIntegrand chi x + originDoublePoleCorrection chi) z
  exact (le_min hOriginal hCorrectionSimple).trans
    (meromorphicOrderAt_add
      (meromorphic_explicitFormulaIntegrand hchi x hx z)
      hCorrectionAnalytic.meromorphicAt)

end BombieriVinogradov.SiegelWalfisz
