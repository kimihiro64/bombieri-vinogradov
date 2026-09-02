import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.IntegrandSimpleAwayZero
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Regularized residues away from the origin

This module proves that the origin correction does not change residues at
nonzero points.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The origin-regularized integrand has the same residue as the original
explicit-formula integrand at every nonzero point. -/
theorem residue_regularizedExplicitFormulaIntegrand_eq_of_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x)
    {rho : Complex} (hrho : Ne rho 0) :
    residue (regularizedExplicitFormulaIntegrand chi x) rho =
      residue (explicitFormulaIntegrand chi x) rho := by
  let f : Complex -> Complex := explicitFormulaIntegrand chi x
  have hf : MeromorphicAt f rho := by
    simpa [f] using meromorphic_explicitFormulaIntegrand hchi x hx rho
  have hSimple : HasSimplePolesOn f ({rho} : Set Complex) := by
    simpa [f] using
      hasSimplePolesOn_explicitFormulaIntegrand_away_zero
        hchi x hx ({rho} : Set Complex) (by simpa using hrho.symm)
  have hOrder : (-1 : WithTop Int) <= meromorphicOrderAt f rho :=
    hSimple rho (by simp)
  have hLinear : MeromorphicAt (fun z : Complex => z - rho) rho := by
    fun_prop
  have hProduct : MeromorphicAt (fun z : Complex => (z - rho) * f z) rho :=
    hLinear.mul hf
  have hProductOrder :
      0 <= meromorphicOrderAt (fun z : Complex => (z - rho) * f z) rho := by
    change 0 <= meromorphicOrderAt ((fun z : Complex => z - rho) * f) rho
    rw [meromorphicOrderAt_mul hLinear hf, meromorphicOrderAt_id_sub_const]
    have hadd := add_le_add_left hOrder (1 : WithTop Int)
    simpa [add_comm] using hadd
  have hOriginalExists :
      exists c, Filter.Tendsto (fun z : Complex => (z - rho) * f z)
        (nhdsWithin rho (Compl.compl ({rho} : Set Complex))) (nhds c) :=
    tendsto_nhds_of_meromorphicOrderAt_nonneg hProduct hProductOrder
  have hOriginalTendsto :
      Filter.Tendsto (fun z : Complex => (z - rho) * f z)
        (nhdsWithin rho (Compl.compl ({rho} : Set Complex)))
        (nhds (residue f rho)) := by
    simpa [residue] using tendsto_nhds_limUnder hOriginalExists
  have hCorrectionContinuous :
      ContinuousAt (originDoublePoleCorrection chi) rho := by
    unfold originDoublePoleCorrection
    exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hrho)
  have hSubTendsto :
      Filter.Tendsto (fun z : Complex => z - rho)
        (nhdsWithin rho (Compl.compl ({rho} : Set Complex))) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr
      (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
  have hCorrectionTendsto :
      Filter.Tendsto
        (fun z : Complex => (z - rho) * originDoublePoleCorrection chi z)
        (nhdsWithin rho (Compl.compl ({rho} : Set Complex))) (nhds 0) := by
    simpa using
      hSubTendsto.mul
        (hCorrectionContinuous.tendsto.mono_left nhdsWithin_le_nhds)
  apply residue_eq_of_tendsto
  have hSum := hOriginalTendsto.add hCorrectionTendsto
  simpa [regularizedExplicitFormulaIntegrand, f, mul_add] using hSum

end BombieriVinogradov.SiegelWalfisz
