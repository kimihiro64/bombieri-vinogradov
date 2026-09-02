import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# High-height optimization for a quadratic zero

This pure real argument formalizes equation (408). A lower bound for `L * t`
controls the zeta pole term, after which one explicit choice of
`sigma - 1 = delta / L` gives a uniform reciprocal-`L` horizontal gap.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_highHeight_gap_of_core
    {K eta : Real} (hK : 0 < K) (heta : 0 < eta) :
    exists c : Real, 0 < c ∧
      forall {beta L t : Real}, beta < 1 -> Real.log 3 ≤ L ->
        eta / L ≤ t ->
          (forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
            4 * (sigma - beta)⁻¹ ≤
              3 * (sigma - 1)⁻¹ +
                (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2) +
                K * L) ->
            c / L ≤ 1 - beta := by
  let delta : Real :=
    min (8 * K)⁻¹ (min (eta / 2) (Real.log 3 / 2))
  let c : Real := delta / 16
  let M : Real := 3 / delta + delta / (4 * eta ^ 2) + K
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hDeltaPos : 0 < delta := by
    dsimp [delta]
    exact lt_min (inv_pos.mpr (mul_pos (by norm_num) hK))
      (lt_min (half_pos heta) (half_pos hLogThree))
  have hDeltaLeK : delta ≤ (8 * K)⁻¹ := by
    dsimp [delta]
    exact min_le_left _ _
  have hDeltaLeEta : delta ≤ eta / 2 := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hDeltaLeLog : delta ≤ Real.log 3 / 2 := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hKDelta : K * delta ≤ 1 / 8 := by
    calc
      K * delta ≤ K * (8 * K)⁻¹ :=
        mul_le_mul_of_nonneg_left hDeltaLeK hK.le
      _ = 1 / 8 := by
        field_simp
  have hDeltaSq : delta ^ 2 ≤ eta ^ 2 / 4 := by
    nlinarith [sq_nonneg (eta / 2 - delta)]
  have hEtaSqPos : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hFraction : delta ^ 2 / (4 * eta ^ 2) ≤ 1 / 16 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hEtaSqPos)).2
    nlinarith
  have hMPos : 0 < M := by
    dsimp [M]
    positivity
  have hMDeltaIdentity :
      M * delta = 3 + delta ^ 2 / (4 * eta ^ 2) + K * delta := by
    dsimp [M]
    field_simp
  have hMDelta : M * delta ≤ 13 / 4 := by
    rw [hMDeltaIdentity]
    linarith
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  refine Exists.intro c (And.intro hcPos ?_)
  intro beta L t hbeta hL hHeight hcore
  let d : Real := 1 - beta
  let x : Real := delta / L
  have hLPos : 0 < L := hLogThree.trans_le hL
  have hdPos : 0 < d := sub_pos.mpr hbeta
  have hxPos : 0 < x := div_pos hDeltaPos hLPos
  have hDeltaLeLHalf : delta ≤ L / 2 := by
    linarith
  have hxLeHalf : x ≤ 1 / 2 := by
    dsimp [x]
    apply (div_le_iff₀ hLPos).2
    nlinarith
  have hcoreAt := hcore (1 + x) (by linarith) (by linarith)
  have hSigmaBeta : 1 + x - beta = x + d := by
    dsimp [d]
    ring
  have hSigmaOne : 1 + x - 1 = x := by ring
  have hxInv : x⁻¹ = L / delta := by
    dsimp [x]
    field_simp
  rw [hSigmaBeta, hSigmaOne, hxInv] at hcoreAt
  have hHeightBasePos : 0 < eta / L := div_pos heta hLPos
  have htPos : 0 < t := hHeightBasePos.trans_le hHeight
  have hHeightSq : (eta / L) ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t - eta / L)]
  have hBaseDenominatorPos : 0 < 4 * (eta / L) ^ 2 := by
    positivity
  have hDenominatorLower :
      4 * (eta / L) ^ 2 ≤ x ^ 2 + 4 * t ^ 2 := by
    nlinarith [sq_nonneg x]
  have hPoleUpperRaw :
      x / (x ^ 2 + 4 * t ^ 2) ≤
        x / (4 * (eta / L) ^ 2) :=
    div_le_div_of_nonneg_left hxPos.le hBaseDenominatorPos
      hDenominatorLower
  have hPoleIdentity :
      x / (4 * (eta / L) ^ 2) =
        delta * L / (4 * eta ^ 2) := by
    dsimp [x]
    field_simp
  have hPoleUpper :
      x / (x ^ 2 + 4 * t ^ 2) ≤
        delta * L / (4 * eta ^ 2) := by
    rw [← hPoleIdentity]
    exact hPoleUpperRaw
  have hRightIdentity :
      3 * (L / delta) + delta * L / (4 * eta ^ 2) + K * L =
        L * M := by
    dsimp [M]
    ring
  have hCoreBound : 4 * (x + d)⁻¹ ≤ L * M := by
    calc
      4 * (x + d)⁻¹ ≤
          3 * (L / delta) +
            x / (x ^ 2 + 4 * t ^ 2) + K * L := hcoreAt
      _ ≤ 3 * (L / delta) +
          delta * L / (4 * eta ^ 2) + K * L := by
        linarith
      _ = L * M := hRightIdentity
  have hDenominatorPos : 0 < x + d := add_pos hxPos hdPos
  have hMultiplied : 4 ≤ L * M * (x + d) :=
    (mul_inv_le_iff₀ hDenominatorPos).mp hCoreBound
  change c / L ≤ d
  by_contra hGap
  have hdUpper : d < c / L := lt_of_not_ge hGap
  have hXDUpper : x + d < (delta + c) / L := by
    calc
      x + d = delta / L + d := by rfl
      _ < delta / L + c / L := by
        simpa [add_comm] using add_lt_add_left hdUpper (delta / L)
      _ = (delta + c) / L := by ring
  have hLMPos : 0 < L * M := mul_pos hLPos hMPos
  have hProductUpper :
      L * M * (x + d) < L * M * ((delta + c) / L) :=
    mul_lt_mul_of_pos_left hXDUpper hLMPos
  have hProductIdentity :
      L * M * ((delta + c) / L) = M * (delta + c) := by
    field_simp
  rw [hProductIdentity] at hProductUpper
  have hFinalUpper : M * (delta + c) < 4 := by
    calc
      M * (delta + c) = (17 / 16 : Real) * (M * delta) := by
        dsimp [c]
        ring
      _ ≤ (17 / 16 : Real) * (13 / 4) :=
        mul_le_mul_of_nonneg_left hMDelta (by norm_num)
      _ < 4 := by norm_num
  linarith

end BombieriVinogradov.SiegelWalfisz
