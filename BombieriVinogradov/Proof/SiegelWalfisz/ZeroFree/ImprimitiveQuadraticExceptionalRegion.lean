import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ImprimitiveLFunctionZero
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticLFunctionExceptionalRegion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Quadratic exceptional region at an arbitrary character level

This module transfers the primitive quadratic exceptional region to an
imprimitive character. Zero values and heights are preserved exactly; only
the conductor logarithm is weakened to the ambient-level logarithm.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_imprimitive_quadratic_LFunction_exceptionalRegion :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        chi ≠ 1 -> chi ^ 2 = 1 ->
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            s.im ≠ 0 ->
              c / (Real.log N + Real.log (|s.im| + 2)) ≤ 1 - s.re) ∧
          (forall s t : Complex,
            0 < s.re -> 0 < t.re ->
            chi.LFunction s = 0 -> chi.LFunction t = 0 ->
            s.im = 0 -> t.im = 0 ->
            1 - s.re ≤ c / Real.log N ->
            1 - t.re ≤ c / Real.log N -> s = t) ∧
          (forall s : Complex, 0 < s.re -> chi.LFunction s = 0 ->
            s.im = 0 -> 1 - s.re ≤ c / Real.log N ->
              analyticOrderNatAt chi.LFunction s = 1) := by
  obtain ⟨c, hcPos, hPrimitiveRegion⟩ :=
    exists_primitive_quadratic_LFunction_exceptionalRegion
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN chi hchi hchiSquare
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hPrimitiveNe :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi
  have hPrimitiveSquare :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one
      chi hchiSquare
  have hConductorLower :=
    BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one
      chi hchi
  have hConductorLevel :=
    BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hRegion := hPrimitiveRegion hConductorLower hPrimitiveNe
    chi.primitiveCharacter_isPrimitive hPrimitiveSquare
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogConductorLower : Real.log 3 ≤ Real.log chi.conductor :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hConductorLower)
  have hLogConductorPos : 0 < Real.log chi.conductor :=
    hLogThree.trans_le hLogConductorLower
  have hLogConductorLevel : Real.log chi.conductor ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast NeZero.pos chi.conductor)
      (by exact_mod_cast hConductorLevel)
  have hRealRatio : c / Real.log N ≤ c / Real.log chi.conductor :=
    div_le_div_of_nonneg_left hcPos.le hLogConductorPos hLogConductorLevel
  apply And.intro
  · intro s hs hzero hsNonreal
    have hPrimitiveZero :=
      primitive_LFunction_eq_zero_of_LFunction_eq_zero
        chi hchi hs hzero
    have hPrimitiveGap := hRegion.1 s hs hPrimitiveZero hsNonreal
    have hHeightNonneg : 0 ≤ Real.log (|s.im| + 2) := by
      apply Real.log_nonneg
      linarith [abs_nonneg s.im]
    have hPrimitiveDenominatorPos :
        0 < Real.log chi.conductor + Real.log (|s.im| + 2) := by
      linarith
    have hDenominatorLe :
        Real.log chi.conductor + Real.log (|s.im| + 2) ≤
          Real.log N + Real.log (|s.im| + 2) :=
      add_le_add hLogConductorLevel le_rfl
    have hRatio :
        c / (Real.log N + Real.log (|s.im| + 2)) ≤
          c / (Real.log chi.conductor + Real.log (|s.im| + 2)) :=
      div_le_div_of_nonneg_left hcPos.le
        hPrimitiveDenominatorPos hDenominatorLe
    exact hRatio.trans hPrimitiveGap
  · apply And.intro
    · intro s t hs ht hsZero htZero hsReal htReal hsGap htGap
      have hsPrimitiveZero :=
        primitive_LFunction_eq_zero_of_LFunction_eq_zero
          chi hchi hs hsZero
      have htPrimitiveZero :=
        primitive_LFunction_eq_zero_of_LFunction_eq_zero
          chi hchi ht htZero
      exact hRegion.2.1 s t hs ht hsPrimitiveZero htPrimitiveZero
        hsReal htReal (hsGap.trans hRealRatio) (htGap.trans hRealRatio)
    · intro s hs hzero hsReal hsGap
      have hPrimitiveZero :=
        primitive_LFunction_eq_zero_of_LFunction_eq_zero
          chi hchi hs hzero
      have hPrimitiveOrder := hRegion.2.2 s hs hPrimitiveZero
        hsReal (hsGap.trans hRealRatio)
      have hOrderBridge :=
        analyticOrderNatAt_LFunction_eq_primitive chi hchi hs
      exact hOrderBridge.trans hPrimitiveOrder

end BombieriVinogradov.SiegelWalfisz
