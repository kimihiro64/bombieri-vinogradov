import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLFunctionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndexOfLFunctionZero
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticExceptionalRegion

/-!
# Primitive quadratic exceptional region for ordinary L-functions

This module transfers the completed-function exceptional region to ordinary
Dirichlet L-function zeros in the positive half-plane, preserving zero values
and analytic orders.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_LFunction_exceptionalRegion :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
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
  obtain ⟨c, hcPos, hCompleted⟩ :=
    exists_primitive_quadratic_exceptionalRegion
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive hchiSquare
  have hRegion := hCompleted hNLower hchi hPrimitive hchiSquare
  apply And.intro
  · intro s hs hzero hsNonreal
    obtain ⟨p, hp⟩ :=
      exists_completedZeroIndex_of_LFunction_eq_zero
        hchi hPrimitive hs hzero
    have hpNonreal :
        (Complex.Hadamard.divisorZeroIndex₀_val p).im ≠ 0 := by
      rw [hp]
      exact hsNonreal
    have hGap := hRegion.1 p hpNonreal
    simpa [hp] using hGap
  · apply And.intro
    · intro s t hs ht hsZero htZero hsReal htReal hsGap htGap
      obtain ⟨p, hp⟩ :=
        exists_completedZeroIndex_of_LFunction_eq_zero
          hchi hPrimitive hs hsZero
      obtain ⟨q, hq⟩ :=
        exists_completedZeroIndex_of_LFunction_eq_zero
          hchi hPrimitive ht htZero
      have hpReal :
          (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 := by
        rw [hp]
        exact hsReal
      have hqReal :
          (Complex.Hadamard.divisorZeroIndex₀_val q).im = 0 := by
        rw [hq]
        exact htReal
      have hpGap :
          1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
            c / Real.log N := by
        rw [hp]
        exact hsGap
      have hqGap :
          1 - (Complex.Hadamard.divisorZeroIndex₀_val q).re ≤
            c / Real.log N := by
        rw [hq]
        exact htGap
      have hpq := hRegion.2.1 p q hpReal hqReal hpGap hqGap
      calc
        s = Complex.Hadamard.divisorZeroIndex₀_val p := hp.symm
        _ = Complex.Hadamard.divisorZeroIndex₀_val q := congrArg _ hpq
        _ = t := hq
    · intro s hs hzero hsReal hsGap
      obtain ⟨p, hp⟩ :=
        exists_completedZeroIndex_of_LFunction_eq_zero
          hchi hPrimitive hs hzero
      have hpReal :
          (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 := by
        rw [hp]
        exact hsReal
      have hpGap :
          1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
            c / Real.log N := by
        rw [hp]
        exact hsGap
      have hCompletedOrder := hRegion.2.2 p hpReal hpGap
      rw [hp] at hCompletedOrder
      have hOrderBridge :=
        analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction
          hchi hs
      exact hOrderBridge.symm.trans hCompletedOrder

end BombieriVinogradov.SiegelWalfisz
