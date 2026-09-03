import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.CenteredZeroDifferenceNorm
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.DifferenceCardBound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform centered zero-cutoff transfer

This module combines the isolated multiplicity count and finite-sum majorant
into the logarithmic error for moving the zero cutoff through one unit.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_centeredTruncatedCriticalZeroSum_cutoffTransfer_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 < x ->
              forall {T Tprime : Real}, 2 <= T -> T <= Tprime ->
                Tprime <= T + 1 ->
                  forall exceptional : Option Complex,
                    norm
                        (centeredTruncatedCriticalZeroSum
                            chi x Tprime exceptional -
                          centeredTruncatedCriticalZeroSum
                            chi x T exceptional) <=
                      C * ((x : Real) / T * zeroHeightLogScale N T)) := by
  choose C0 hC0Pos hCard using
    exists_card_retainedCriticalZeroCutoffDifference_le
  refine Exists.intro (4 * C0) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive x hx
    T Tprime hT hCutoff hTop exceptional
  have hCount :=
    hCard hN hchi hPrimitive (T := T) (Tprime := Tprime)
      hT hTop exceptional
  have hSum :=
    norm_centeredTruncatedCriticalZeroSum_sub_le_card_mul
      chi hx hT hCutoff exceptional
  have hTPos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hMajorantNonneg : 0 <= 4 * (x : Real) / T := by positivity
  have hProduct :=
    mul_le_mul_of_nonneg_right hCount hMajorantNonneg
  calc
    norm
          (centeredTruncatedCriticalZeroSum chi x Tprime exceptional -
            centeredTruncatedCriticalZeroSum chi x T exceptional) <=
        ((retainedCriticalZeroCutoffDifference
            chi T Tprime exceptional).card : Real) *
          (4 * (x : Real) / T) :=
      hSum
    _ <= (C0 * zeroHeightLogScale N T) *
          (4 * (x : Real) / T) :=
      hProduct
    _ = (4 * C0) * ((x : Real) / T * zeroHeightLogScale N T) := by
      ring

end BombieriVinogradov.SiegelWalfisz
