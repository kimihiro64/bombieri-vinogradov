import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real optimization behind the complex zero-free region

Choosing `sigma - 1 = 1 / (2 K L)` in the pre-optimization inequality gives
the explicit lower bound `1 - beta >= 1 / (14 K L)`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem core_inequality_implies_gap
    {beta K L : Real} (hbeta : beta < 1) (hK : 0 < K) (hL : 0 < L)
    (hKL : 1 ≤ K * L)
    (hcore : forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
      4 * (sigma - beta)⁻¹ ≤ 3 * (sigma - 1)⁻¹ + K * L) :
    (14 * K * L)⁻¹ ≤ 1 - beta := by
  let Q := K * L
  let delta := 1 - beta
  let x := (2 * Q)⁻¹
  have hQPos : 0 < Q := mul_pos hK hL
  have hDeltaPos : 0 < delta := sub_pos.mpr hbeta
  have hTwoQPos : 0 < 2 * Q := mul_pos (by norm_num) hQPos
  have hxPos : 0 < x := inv_pos.mpr hTwoQPos
  have hTwoLe : (2 : Real) ≤ 2 * Q := by
    dsimp [Q]
    nlinarith
  have hxLeHalf : x ≤ (2 : Real)⁻¹ := by
    exact (inv_le_inv₀ hTwoQPos (by norm_num)).2 hTwoLe
  have hxLeOne : x ≤ 1 := by
    calc
      x ≤ (2 : Real)⁻¹ := hxLeHalf
      _ ≤ 1 := by norm_num
  have hcoreAt := hcore (1 + x) (by linarith) (by linarith)
  have hQL : K * L = Q := rfl
  have hxInv : x⁻¹ = 2 * Q := by
    dsimp [x]
    rw [inv_inv]
  have hSigmaBeta : 1 + x - beta = x + delta := by
    dsimp [delta]
    ring
  have hSigmaOne : 1 + x - 1 = x := by ring
  have hCoreNormalized : 4 * (x + delta)⁻¹ ≤ 7 * Q := by
    rw [hSigmaBeta, hSigmaOne, hxInv, hQL] at hcoreAt
    nlinarith
  have hDenominatorPos : 0 < x + delta := add_pos hxPos hDeltaPos
  have hMultiplied : 4 ≤ 7 * Q * (x + delta) :=
    (mul_inv_le_iff₀ hDenominatorPos).mp hCoreNormalized
  have hQx : Q * x = 1 / 2 := by
    dsimp [x]
    field_simp
  have hGapScaled : 1 / 2 ≤ 7 * Q * delta := by
    nlinarith
  have hTarget : (14 * Q)⁻¹ ≤ delta := by
    have hFourteenQPos : 0 < 14 * Q := mul_pos (by norm_num) hQPos
    have hOne : 1 ≤ delta * (14 * Q) := by
      nlinarith
    have hOneInv : 1 * (14 * Q)⁻¹ ≤ delta :=
      (mul_inv_le_iff₀ hFourteenQPos).2 hOne
    simpa only [one_mul] using hOneInv
  simpa [Q, delta, mul_assoc] using hTarget

end BombieriVinogradov.SiegelWalfisz
