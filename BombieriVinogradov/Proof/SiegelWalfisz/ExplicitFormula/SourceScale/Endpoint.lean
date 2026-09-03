import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Coefficient
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Half-sum endpoint versus the source scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_half_mul_twistedMangoldtSequence_le_sourceScale
    {N x : Nat} (chi : DirichletCharacter Complex N)
    (hN : 3 <= N) (hx : 2 < x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    norm ((1 / 2 : Complex) * twistedMangoldtSequence chi x) <=
      (x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2 := by
  let L := Real.log ((N * x : Nat) : Real)
  have hLOne : 1 <= L := by
    simpa [L] using one_le_log_level_mul_argument hN hx
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hLSqProduct : 0 <= (L - 1) * L :=
    mul_nonneg (sub_nonneg.mpr hLOne) hLNonneg
  have hLSq : L <= L ^ 2 := by
    nlinarith
  have hLogX : Real.log x <= L := by
    simpa [L] using log_argument_le_log_level_mul_argument hN hx
  have hLambda :
      norm (twistedMangoldtSequence chi x) <= Real.log x :=
    (norm_twistedMangoldtSequence_le_vonMangoldt chi x).trans
      ArithmeticFunction.vonMangoldt_le_log
  have hHalf :
      norm ((1 / 2 : Complex) * twistedMangoldtSequence chi x) <=
        (1 / 2 : Real) * Real.log x := by
    calc
      norm ((1 / 2 : Complex) * twistedMangoldtSequence chi x) =
          (1 / 2 : Real) * norm (twistedMangoldtSequence chi x) := by
        rw [norm_mul]
        norm_num
      _ <= (1 / 2 : Real) * Real.log x :=
        mul_le_mul_of_nonneg_left hLambda (by positivity)
  have hHalfSq : (1 / 2 : Real) * Real.log x <= L ^ 2 := by
    nlinarith
  have hTPos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hRatioRaw : T / T <= (x : Real) / T :=
    (div_le_div_iff_of_pos_right hTPos).2 hTx
  have hRatioOne : 1 <= (x : Real) / T := by
    simpa [ne_of_gt hTPos] using hRatioRaw
  calc
    norm ((1 / 2 : Complex) * twistedMangoldtSequence chi x) <=
        (1 / 2 : Real) * Real.log x :=
      hHalf
    _ <= L ^ 2 :=
      hHalfSq
    _ <= (x : Real) / T * L ^ 2 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hRatioOne (sq_nonneg L)
    _ = (x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2 := by
      rfl

end BombieriVinogradov.SiegelWalfisz
