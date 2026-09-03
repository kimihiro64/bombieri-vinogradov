import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.SelectedHeightLogs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Left boundary term versus the source scale
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem leftBoundaryMajorant_le_sourceScale
    {N x : Nat} {CLeft : Real} (hCLeft : 0 <= CLeft)
    (hN : 3 <= N) (hx : 2 < x)
    {T Tprime : Real} (hT : 2 <= T) (hTx : T <= x)
    (hLower : T <= Tprime) (hUpper : Tprime <= T + 1) :
    (6 / Real.pi) *
        (abs (Real.log N) + CLeft * Real.log (Tprime + 2)) *
          Real.log (Tprime + 1) <=
      (6 / Real.pi) * (1 + CLeft) *
        ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2) := by
  let L := Real.log ((N * x : Nat) : Real)
  have hLOne : 1 <= L := by
    simpa [L] using one_le_log_level_mul_argument hN hx
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hLevel :
      abs (Real.log N) <= L := by
    simpa [L] using abs_log_level_le_log_level_mul_argument hN hx
  have hHeightTwo :
      Real.log (Tprime + 2) <= L := by
    simpa [L] using
      log_selectedHeight_add_two_le_log_level_mul_argument
        hN hx hT hLower hUpper hTx
  have hHeightOne :
      Real.log (Tprime + 1) <= L := by
    simpa [L] using
      log_selectedHeight_add_one_le_log_level_mul_argument
        hN hx hT hLower hUpper hTx
  have hHeightTwoNonneg : 0 <= Real.log (Tprime + 2) :=
    Real.log_nonneg (by linarith)
  have hHeightOneNonneg : 0 <= Real.log (Tprime + 1) :=
    Real.log_nonneg (by linarith)
  have hFirst :
      abs (Real.log N) + CLeft * Real.log (Tprime + 2) <=
        (1 + CLeft) * L := by
    calc
      abs (Real.log N) + CLeft * Real.log (Tprime + 2) <=
          L + CLeft * L :=
        add_le_add hLevel
          (mul_le_mul_of_nonneg_left hHeightTwo hCLeft)
      _ = (1 + CLeft) * L := by ring
  have hUpperFirstNonneg : 0 <= (1 + CLeft) * L :=
    mul_nonneg (by linarith) hLNonneg
  have hLogProduct :
      (abs (Real.log N) + CLeft * Real.log (Tprime + 2)) *
          Real.log (Tprime + 1) <=
        (1 + CLeft) * L * L := by
    apply
      (mul_le_mul_of_nonneg_right hFirst hHeightOneNonneg).trans
    exact mul_le_mul_of_nonneg_left hHeightOne hUpperFirstNonneg
  have hPiFactorNonneg : 0 <= 6 / Real.pi := by positivity
  have hBoundaryLog :
      (6 / Real.pi) *
          ((abs (Real.log N) + CLeft * Real.log (Tprime + 2)) *
            Real.log (Tprime + 1)) <=
        (6 / Real.pi) * ((1 + CLeft) * L * L) :=
    mul_le_mul_of_nonneg_left hLogProduct hPiFactorNonneg
  have hTPos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hRatioRaw : T / T <= (x : Real) / T :=
    (div_le_div_iff_of_pos_right hTPos).2 hTx
  have hRatioOne : 1 <= (x : Real) / T := by
    simpa [ne_of_gt hTPos] using hRatioRaw
  have hAbsorb :
      L ^ 2 <= (x : Real) / T * L ^ 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hRatioOne (sq_nonneg L)
  calc
    (6 / Real.pi) *
        (abs (Real.log N) + CLeft * Real.log (Tprime + 2)) *
          Real.log (Tprime + 1) =
      (6 / Real.pi) *
        ((abs (Real.log N) + CLeft * Real.log (Tprime + 2)) *
          Real.log (Tprime + 1)) := by ring
    _ <= (6 / Real.pi) * ((1 + CLeft) * L * L) :=
      hBoundaryLog
    _ = (6 / Real.pi) * (1 + CLeft) * L ^ 2 := by
      ring
    _ <= (6 / Real.pi) * (1 + CLeft) *
        ((x : Real) / T * L ^ 2) := by
      have hCoeff : 0 <= (6 / Real.pi) * (1 + CLeft) :=
        mul_nonneg hPiFactorNonneg (by linarith)
      apply mul_le_mul_of_nonneg_left hAbsorb hCoeff
    _ = (6 / Real.pi) * (1 + CLeft) *
        ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2) := by
      rfl

end BombieriVinogradov.SiegelWalfisz
