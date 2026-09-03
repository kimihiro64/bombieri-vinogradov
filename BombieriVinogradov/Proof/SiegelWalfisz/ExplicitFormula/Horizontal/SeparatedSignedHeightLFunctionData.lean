import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.QuantitativeLFunctionNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.SeparatedSignedHeightLogDerivativeBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# L-function data from separation at one signed height

This module pairs quantitative-gap nonvanishing with the selector-independent
log-squared derivative estimate at one arbitrary signed horizontal height.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_LFunction_data_of_separation :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {T K L : Real} {s : Complex},
              s.im = T ->
              -(1 : Real) / 2 <= s.re ->
              s.re <= 2 ->
              2 <= abs T ->
              Ne T 0 ->
              0 < K ->
              1 <= L ->
              Real.log N + Real.log (abs T + 2) <= L ->
              (forall p : SymmetricCompletedZeroIndex chi,
                1 / (K * L) <=
                  abs (T - (symmetricCompletedZeroValue p).im)) ->
                And (Ne (chi.LFunction s) 0)
                  (norm (logDeriv chi.LFunction s) <=
                    C * (K + 1) * L ^ 2)) := by
  choose C hCPos hBound using
    exists_norm_logDeriv_LFunction_le_sq_of_separation
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T K L s hsIm hsLower hsUpper
    hAbsT hT hK hLOne hScaleLe hGap
  have hLPos : 0 < L :=
    zero_lt_one.trans_le hLOne
  have hNonzero : Ne (chi.LFunction s) 0 :=
    LFunction_ne_zero_of_completedZero_ordinate_gap
      hchi hPrimitive hsIm hsLower hT (mul_pos hK hLPos) hGap
  exact And.intro hNonzero
    (hBound hN hchi hPrimitive hsIm hsLower hsUpper hAbsT
      hNonzero hK hLOne hScaleLe hGap)

end BombieriVinogradov.SiegelWalfisz
