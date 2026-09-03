import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.PerronApproximation
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centered Perron error versus the source scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_centeredVerticalIntegral_sub_halfSum_le_sourceScale :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall chi : DirichletCharacter Complex N,
          forall {x : Nat}, 2 < x ->
            forall {T Tprime : Real}, 2 <= T -> T <= x ->
              T <= Tprime ->
                norm
                    (centeredExplicitFormulaVerticalIntegral chi x
                        (optimizedPerronLine x) Tprime -
                      characterChebyshevHalfSum x chi) <=
                  C * ((x : Real) / T *
                    (Real.log ((N * x : Nat) : Real)) ^ 2)) := by
  choose C0 hC0Pos hPerron using
    exists_norm_centeredVerticalIntegral_sub_halfSum_le_optimized
  refine Exists.intro (2 * C0) (And.intro (by positivity) ?_)
  intro N inst hN chi x hx T Tprime hT hTx hLower
  let L := Real.log ((N * x : Nat) : Real)
  let A := (x : Real) / T * L ^ 2
  have hLOne : 1 <= L := by
    simpa [L] using one_le_log_level_mul_argument hN hx
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hLogTwo :
      Real.log (2 * (x : Real)) <= L := by
    simpa [L] using
      log_two_mul_argument_le_log_level_mul_argument hN hx
  have hxPosReal : 0 < (x : Real) :=
    Nat.cast_pos.mpr (lt_trans (by norm_num) hx)
  have hLogTwoNonneg : 0 <= Real.log (2 * (x : Real)) :=
    Real.log_nonneg (by linarith)
  have hSquareProduct :
      0 <= (L - Real.log (2 * (x : Real))) *
        (L + Real.log (2 * (x : Real))) :=
    mul_nonneg (sub_nonneg.mpr hLogTwo)
      (add_nonneg hLNonneg hLogTwoNonneg)
  have hLogTwoSq :
      Real.log (2 * (x : Real)) ^ 2 <= L ^ 2 := by
    nlinarith
  have hTPos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hTprimePos : 0 < Tprime := hTPos.trans_le hLower
  have hNumerator :
      (x : Real) * Real.log (2 * (x : Real)) ^ 2 <=
        (x : Real) * L ^ 2 :=
    mul_le_mul_of_nonneg_left hLogTwoSq hxPosReal.le
  have hPerronTerm :
      (x : Real) * Real.log (2 * (x : Real)) ^ 2 / Tprime <= A := by
    calc
      (x : Real) * Real.log (2 * (x : Real)) ^ 2 / Tprime <=
          (x : Real) * L ^ 2 / Tprime :=
        div_le_div_of_nonneg_right hNumerator hTprimePos.le
      _ <= (x : Real) * L ^ 2 / T :=
        div_le_div_of_nonneg_left
          (mul_nonneg hxPosReal.le (sq_nonneg L)) hTPos hLower
      _ = A := by
        dsimp [A]
        ring
  have hLogX :
      Real.log x <= L := by
    simpa [L] using log_argument_le_log_level_mul_argument hN hx
  have hLSqProduct : 0 <= (L - 1) * L :=
    mul_nonneg (sub_nonneg.mpr hLOne) hLNonneg
  have hLSq : L <= L ^ 2 := by
    nlinarith
  have hRatioRaw : T / T <= (x : Real) / T :=
    (div_le_div_iff_of_pos_right hTPos).2 hTx
  have hRatioOne : 1 <= (x : Real) / T := by
    simpa [ne_of_gt hTPos] using hRatioRaw
  have hSqAbsorb : L ^ 2 <= A := by
    dsimp [A]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hRatioOne (sq_nonneg L)
  have hCenteringLog : Real.log x <= A :=
    hLogX.trans (hLSq.trans hSqAbsorb)
  have hScale :
      (x : Real) * Real.log (2 * (x : Real)) ^ 2 / Tprime +
          Real.log (x : Real) <=
        2 * A := by
    linarith
  have hRaw :=
    hPerron N chi x hx Tprime hTprimePos
  calc
    norm
        (centeredExplicitFormulaVerticalIntegral chi x
            (optimizedPerronLine x) Tprime -
          characterChebyshevHalfSum x chi) <=
      C0 * (((x : Real) * Real.log (2 * (x : Real)) ^ 2 / Tprime) +
        Real.log (x : Real)) :=
      hRaw
    _ <= C0 * (2 * A) :=
      mul_le_mul_of_nonneg_left hScale hC0Pos.le
    _ = (2 * C0) * ((x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2) := by
      dsimp [A, L]
      ring

end BombieriVinogradov.SiegelWalfisz
