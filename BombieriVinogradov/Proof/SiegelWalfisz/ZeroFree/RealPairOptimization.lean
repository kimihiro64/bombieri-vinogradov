import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Optimization for two real zeros

This pure real lemma formalizes the repeated-zero/two-real-zero optimization
described after Strombergsson equation (410).
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem realPair_core_inequality_implies_gap
    {beta Q : Real} (hbeta : beta < 1) (hQ : 0 < Q) (hQOne : 1 ≤ Q)
    (hcore : forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
      2 * (sigma - beta)⁻¹ ≤ (sigma - 1)⁻¹ + Q) :
    (15 * Q)⁻¹ ≤ 1 - beta := by
  let d := 1 - beta
  let x := (5 * Q)⁻¹
  have hdPos : 0 < d := sub_pos.mpr hbeta
  have hFiveQPos : 0 < 5 * Q := mul_pos (by norm_num) hQ
  have hxPos : 0 < x := inv_pos.mpr hFiveQPos
  have hFiveLe : (5 : Real) ≤ 5 * Q := by nlinarith
  have hxLe : x ≤ (5 : Real)⁻¹ :=
    (inv_le_inv₀ hFiveQPos (by norm_num)).2 hFiveLe
  have hcoreAt := hcore (1 + x) (by linarith) (by linarith)
  have hxInv : x⁻¹ = 5 * Q := by
    dsimp [x]
    rw [inv_inv]
  have hSigmaBeta : 1 + x - beta = x + d := by
    dsimp [d]
    ring
  have hSigmaOne : 1 + x - 1 = x := by ring
  rw [hSigmaBeta, hSigmaOne, hxInv] at hcoreAt
  have hDenominatorPos : 0 < x + d := add_pos hxPos hdPos
  have hMultiplied : 2 ≤ 6 * Q * (x + d) := by
    apply (mul_inv_le_iff₀ hDenominatorPos).mp
    nlinarith
  have hQx : Q * x = 1 / 5 := by
    dsimp [x]
    field_simp
  have hFifteenQPos : 0 < 15 * Q := mul_pos (by norm_num) hQ
  have hOne : 1 ≤ d * (15 * Q) := by
    nlinarith
  have hOneInv : 1 * (15 * Q)⁻¹ ≤ d :=
    (mul_inv_le_iff₀ hFifteenQPos).2 hOne
  simpa [d] using hOneInv

end BombieriVinogradov.SiegelWalfisz
