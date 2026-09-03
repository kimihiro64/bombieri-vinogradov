import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ZeroCutoffTransfer
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.ZeroHeight
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zero-cutoff transfer versus the source scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_centeredTruncatedCriticalZeroSum_cutoffTransfer_le_sourceScale :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 < x ->
              forall {T Tprime : Real}, 2 <= T -> T <= x ->
                T <= Tprime -> Tprime <= T + 1 ->
                  forall exceptional : Option Complex,
                    norm
                        (centeredTruncatedCriticalZeroSum
                            chi x Tprime exceptional -
                          centeredTruncatedCriticalZeroSum
                            chi x T exceptional) <=
                      C * ((x : Real) / T *
                        (Real.log ((N * x : Nat) : Real)) ^ 2)) := by
  choose C0 hC0Pos hTransfer using
    exists_norm_centeredTruncatedCriticalZeroSum_cutoffTransfer_le
  refine Exists.intro (3 * C0) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive x hx
    T Tprime hT hTx hLower hUpper exceptional
  let L := Real.log ((N * x : Nat) : Real)
  have hLOne : 1 <= L := by
    simpa [L] using one_le_log_level_mul_argument hN hx
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hLSqProduct : 0 <= (L - 1) * L :=
    mul_nonneg (sub_nonneg.mpr hLOne) hLNonneg
  have hLSq : L <= L ^ 2 := by
    nlinarith
  have hZeroHeight :=
    zeroHeightLogScale_le_three_mul_sourceLog hN hx hT hTx
  have hZeroHeightSq :
      zeroHeightLogScale N T <= 3 * L ^ 2 := by
    exact hZeroHeight.trans
      (mul_le_mul_of_nonneg_left hLSq (by positivity))
  have hTNonneg : 0 <= T :=
    le_trans (by positivity) hT
  have hRatioNonneg : 0 <= (x : Real) / T :=
    div_nonneg (Nat.cast_nonneg x) hTNonneg
  have hScaled :
      (x : Real) / T * zeroHeightLogScale N T <=
        (x : Real) / T * (3 * L ^ 2) :=
    mul_le_mul_of_nonneg_left hZeroHeightSq hRatioNonneg
  have hRaw :=
    hTransfer hN hchi hPrimitive hx hT hLower hUpper exceptional
  calc
    norm
        (centeredTruncatedCriticalZeroSum chi x Tprime exceptional -
          centeredTruncatedCriticalZeroSum chi x T exceptional) <=
      C0 * ((x : Real) / T * zeroHeightLogScale N T) :=
      hRaw
    _ <= C0 * ((x : Real) / T * (3 * L ^ 2)) :=
      mul_le_mul_of_nonneg_left hScaled hC0Pos.le
    _ = (3 * C0) * ((x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2) := by
      dsimp [L]
      ring

end BombieriVinogradov.SiegelWalfisz
