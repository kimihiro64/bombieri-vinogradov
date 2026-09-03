import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum

/-!
# Completed-zero avoidance from L-function nonvanishing

This module transports a nonzero Dirichlet L-function value through the
completed normalization and exposes pointwise avoidance of every indexed
completed zero, including multiplicity indices.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem ne_symmetricCompletedZeroValue_of_LFunction_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) {s : Complex}
    (hLFunctionNe : Ne (chi.LFunction s) 0) :
    forall p : SymmetricCompletedZeroIndex chi,
      Ne s (symmetricCompletedZeroValue p) := by
  have hNNeOne : Ne N 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hCompletedValue :=
    chi.LFunction_eq_completed_div_gammaFactor s (Or.inr hNNeOne)
  have hCompletedNe : Ne (chi.completedLFunction s) 0 := by
    intro hCompletedZero
    apply hLFunctionNe
    rw [hCompletedValue, hCompletedZero]
    simp
  have hNCast : Ne (N : Complex) 0 := by
    norm_num [NeZero.ne N]
  have hNormalizationNe : Ne ((N : Complex) ^ (s / 2)) 0 := by
    simp [hNCast]
  have hSymmetricNe : Ne (symmetricCompletedLFunction chi s) 0 := by
    unfold symmetricCompletedLFunction
    exact mul_ne_zero hNormalizationNe hCompletedNe
  intro p hEqual
  apply hSymmetricNe
  rw [hEqual]
  exact symmetricCompletedZeroValue_apply_eq_zero hchi p

end BombieriVinogradov.SiegelWalfisz
