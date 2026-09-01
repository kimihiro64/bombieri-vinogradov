import BombieriVinogradov.Helpers.DirichletCharacter.AbelAnalyticity
import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegralAgreement
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Identification of the Abel integral with the character L-function

This module owns uniqueness of analytic continuation from the
absolute-convergence half-plane.
-/

set_option autoImplicit false

open Filter Set Topology

namespace BombieriVinogradov

/-- The Abel integral agrees with Mathlib's character L-function throughout `re(s)>0`. -/
theorem characterAbelIntegral_eq_LFunction {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1)
    {s : Complex} (hs : 0 < s.re) :
    characterAbelIntegral chi s = ZMod.LFunction chi s := by
  let U : Set Complex := {z : Complex | 0 < z.re}
  have hUOpen : IsOpen U := by
    exact Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hAbel : AnalyticOnNhd Complex (characterAbelIntegral chi) U := by
    exact characterAbelIntegral_analyticOnNhd chi hchi
  have hLFunction : AnalyticOnNhd Complex (ZMod.LFunction chi) U := by
    refine DifferentiableOn.analyticOnNhd (fun z _hz => ?_) hUOpen
    exact (ZMod.differentiableAt_LFunction chi z
      (Or.inr (chi.sum_eq_zero_of_ne_one hchi))).differentiableWithinAt
  have hUPreconnected : IsPreconnected U := by
    exact (convex_halfSpace_re_gt 0).isPreconnected
  have hTwoMem : (2 : Complex) ∈ U := by
    norm_num [U]
  have hAgreementNeighborhood :
      {z : Complex | 1 < z.re} ∈ 𝓝 (2 : Complex) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hAgreement : characterAbelIntegral chi =ᶠ[𝓝 (2 : Complex)] ZMod.LFunction chi :=
    eventually_of_mem hAgreementNeighborhood fun z hz =>
      characterAbelIntegral_eq_LFunction_of_one_lt_re chi hchi hz
  exact hAbel.eqOn_of_preconnected_of_eventuallyEq hLFunction hUPreconnected
    hTwoMem hAgreement hs

end BombieriVinogradov
