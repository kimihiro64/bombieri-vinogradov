import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.SelectedHeightScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.ZeroHeight
import Mathlib.Tactic.Linarith

/-!
# Squared zero-height source-scale bound
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem zeroHeightLogScale_sq_le_nine_mul_sourceLog_sq
    {N x : Nat} [NeZero N] (hN : 3 <= N) (hx : 2 < x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    (zeroHeightLogScale N T) ^ 2 <=
      9 * (Real.log ((N * x : Nat) : Real)) ^ 2 := by
  let Z := zeroHeightLogScale N T
  let L := Real.log ((N * x : Nat) : Real)
  have hZNonneg : 0 <= Z := by
    have hScale :=
      selectedHeight_scale_data
        (N := N) hN hT (Tprime := T) (le_refl T) (by linarith)
    exact zero_le_one.trans hScale.1
  have hLNonneg : 0 <= L := by
    exact zero_le_one.trans
      (by
        simpa [L] using one_le_log_level_mul_argument hN hx)
  have hBound : Z <= 3 * L := by
    simpa [Z, L] using
      zeroHeightLogScale_le_three_mul_sourceLog hN hx hT hTx
  have hProductNonneg :
      0 <= (3 * L - Z) * (3 * L + Z) :=
    mul_nonneg (sub_nonneg.mpr hBound)
      (add_nonneg (mul_nonneg (by norm_num) hLNonneg) hZNonneg)
  dsimp [Z, L] at *
  nlinarith

end BombieriVinogradov.SiegelWalfisz
